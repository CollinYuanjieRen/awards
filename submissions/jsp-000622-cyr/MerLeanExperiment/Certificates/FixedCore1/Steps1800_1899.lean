import MerLeanExperiment.Certificates.FixedCore1.Steps1700_1799

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7681 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c910, some c1357, some c2203, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7681 : lratChecker f7681 p7681 = .success := by decide +kernel
theorem unsat7681 : Unsatisfiable (PosFin 65) f7681 := by
  apply lratCheckerSound f7681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7681
  · intro a ha; simp [p7681] at ha; subst a; trivial
  · exact checked7681
theorem derived7681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7681 := by
  apply localUnsat_implies_entails f7681 [c910, c1357, c2203] c7681 unsat7681 (by rfl) a
  have h0 : Entails.eval a c910 := h 909 (by decide)
  have h1 : Entails.eval a c1357 := h 1356 (by decide)
  have h2 : Entails.eval a c2203 := h 2202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7682 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2057, some c2019, some c2102, some c2513, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p7682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7682 : lratChecker f7682 p7682 = .success := by decide +kernel
theorem unsat7682 : Unsatisfiable (PosFin 65) f7682 := by
  apply lratCheckerSound f7682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7682
  · intro a ha; simp [p7682] at ha; subst a; trivial
  · exact checked7682
theorem derived7682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7682 := by
  apply localUnsat_implies_entails f7682 [c2057, c2019, c2102, c2513] c7682 unsat7682 (by rfl) a
  have h0 : Entails.eval a c2057 := h 2056 (by decide)
  have h1 : Entails.eval a c2019 := h 2018 (by decide)
  have h2 : Entails.eval a c2102 := h 2101 (by decide)
  have h3 : Entails.eval a c2513 := h 2512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7683 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7639, some c7682, some c911, some c2335, some c2120, some c1234, some c1229, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7683 : lratChecker f7683 p7683 = .success := by decide +kernel
theorem unsat7683 : Unsatisfiable (PosFin 65) f7683 := by
  apply lratCheckerSound f7683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7683
  · intro a ha; simp [p7683] at ha; subst a; trivial
  · exact checked7683
theorem derived7683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7683 := by
  apply localUnsat_implies_entails f7683 [c7639, c7682, c911, c2335, c2120, c1234, c1229] c7683 unsat7683 (by rfl) a
  have h0 : Entails.eval a c7639 := derived7639 a h
  have h1 : Entails.eval a c7682 := derived7682 a h
  have h2 : Entails.eval a c911 := h 910 (by decide)
  have h3 : Entails.eval a c2335 := h 2334 (by decide)
  have h4 : Entails.eval a c2120 := h 2119 (by decide)
  have h5 : Entails.eval a c1234 := h 1233 (by decide)
  have h6 : Entails.eval a c1229 := h 1228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7684 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c716, some c7512, some c1304, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7684 : lratChecker f7684 p7684 = .success := by decide +kernel
theorem unsat7684 : Unsatisfiable (PosFin 65) f7684 := by
  apply lratCheckerSound f7684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7684
  · intro a ha; simp [p7684] at ha; subst a; trivial
  · exact checked7684
theorem derived7684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7684 := by
  apply localUnsat_implies_entails f7684 [c716, c7512, c1304] c7684 unsat7684 (by rfl) a
  have h0 : Entails.eval a c716 := h 715 (by decide)
  have h1 : Entails.eval a c7512 := derived7512 a h
  have h2 : Entails.eval a c1304 := h 1303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7685 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7668, some c7677, some c7679, some c7579, some c7616, some c7680, some c7681, some c7683, some c7684, some c1155, some c911, some c2335, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7685 : lratChecker f7685 p7685 = .success := by decide +kernel
theorem unsat7685 : Unsatisfiable (PosFin 65) f7685 := by
  apply lratCheckerSound f7685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7685
  · intro a ha; simp [p7685] at ha; subst a; trivial
  · exact checked7685
theorem derived7685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7685 := by
  apply localUnsat_implies_entails f7685 [c7470, c7626, c7668, c7677, c7679, c7579, c7616, c7680, c7681, c7683, c7684, c1155, c911, c2335] c7685 unsat7685 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7668 := derived7668 a h
  have h3 : Entails.eval a c7677 := derived7677 a h
  have h4 : Entails.eval a c7679 := derived7679 a h
  have h5 : Entails.eval a c7579 := derived7579 a h
  have h6 : Entails.eval a c7616 := derived7616 a h
  have h7 : Entails.eval a c7680 := derived7680 a h
  have h8 : Entails.eval a c7681 := derived7681 a h
  have h9 : Entails.eval a c7683 := derived7683 a h
  have h10 : Entails.eval a c7684 := derived7684 a h
  have h11 : Entails.eval a c1155 := h 1154 (by decide)
  have h12 : Entails.eval a c911 := h 910 (by decide)
  have h13 : Entails.eval a c2335 := h 2334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7686 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7644, some c7643, some c7657, some c1534, some c1380, some c398, some c1084, some c1073, some c1053, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7686 : lratChecker f7686 p7686 = .success := by decide +kernel
theorem unsat7686 : Unsatisfiable (PosFin 65) f7686 := by
  apply lratCheckerSound f7686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7686
  · intro a ha; simp [p7686] at ha; subst a; trivial
  · exact checked7686
theorem derived7686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7686 := by
  apply localUnsat_implies_entails f7686 [c7644, c7643, c7657, c1534, c1380, c398, c1084, c1073, c1053] c7686 unsat7686 (by rfl) a
  have h0 : Entails.eval a c7644 := derived7644 a h
  have h1 : Entails.eval a c7643 := derived7643 a h
  have h2 : Entails.eval a c7657 := derived7657 a h
  have h3 : Entails.eval a c1534 := h 1533 (by decide)
  have h4 : Entails.eval a c1380 := h 1379 (by decide)
  have h5 : Entails.eval a c398 := h 397 (by decide)
  have h6 : Entails.eval a c1084 := h 1083 (by decide)
  have h7 : Entails.eval a c1073 := h 1072 (by decide)
  have h8 : Entails.eval a c1053 := h 1052 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7687 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7643, some c7686, some c392, some c1122, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7687 : lratChecker f7687 p7687 = .success := by decide +kernel
theorem unsat7687 : Unsatisfiable (PosFin 65) f7687 := by
  apply lratCheckerSound f7687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7687
  · intro a ha; simp [p7687] at ha; subst a; trivial
  · exact checked7687
theorem derived7687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7687 := by
  apply localUnsat_implies_entails f7687 [c7643, c7686, c392, c1122] c7687 unsat7687 (by rfl) a
  have h0 : Entails.eval a c7643 := derived7643 a h
  have h1 : Entails.eval a c7686 := derived7686 a h
  have h2 : Entails.eval a c392 := h 391 (by decide)
  have h3 : Entails.eval a c1122 := h 1121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7688 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c968, some c1055, some c1110, some c2020, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p7688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7688 : lratChecker f7688 p7688 = .success := by decide +kernel
theorem unsat7688 : Unsatisfiable (PosFin 65) f7688 := by
  apply lratCheckerSound f7688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7688
  · intro a ha; simp [p7688] at ha; subst a; trivial
  · exact checked7688
theorem derived7688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7688 := by
  apply localUnsat_implies_entails f7688 [c968, c1055, c1110, c2020] c7688 unsat7688 (by rfl) a
  have h0 : Entails.eval a c968 := h 967 (by decide)
  have h1 : Entails.eval a c1055 := h 1054 (by decide)
  have h2 : Entails.eval a c1110 := h 1109 (by decide)
  have h3 : Entails.eval a c2020 := h 2019 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7689 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7668, some c7687, some c7688, some c7608, some c7675, some c7680, some c1122, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7689 : lratChecker f7689 p7689 = .success := by decide +kernel
theorem unsat7689 : Unsatisfiable (PosFin 65) f7689 := by
  apply lratCheckerSound f7689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7689
  · intro a ha; simp [p7689] at ha; subst a; trivial
  · exact checked7689
theorem derived7689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7689 := by
  apply localUnsat_implies_entails f7689 [c7668, c7687, c7688, c7608, c7675, c7680, c1122] c7689 unsat7689 (by rfl) a
  have h0 : Entails.eval a c7668 := derived7668 a h
  have h1 : Entails.eval a c7687 := derived7687 a h
  have h2 : Entails.eval a c7688 := derived7688 a h
  have h3 : Entails.eval a c7608 := derived7608 a h
  have h4 : Entails.eval a c7675 := derived7675 a h
  have h5 : Entails.eval a c7680 := derived7680 a h
  have h6 : Entails.eval a c1122 := h 1121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7690 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7315, some c1384, some c1056, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7690 : lratChecker f7690 p7690 = .success := by decide +kernel
theorem unsat7690 : Unsatisfiable (PosFin 65) f7690 := by
  apply lratCheckerSound f7690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7690
  · intro a ha; simp [p7690] at ha; subst a; trivial
  · exact checked7690
theorem derived7690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7690 := by
  apply localUnsat_implies_entails f7690 [c7315, c1384, c1056] c7690 unsat7690 (by rfl) a
  have h0 : Entails.eval a c7315 := derived7315 a h
  have h1 : Entails.eval a c1384 := h 1383 (by decide)
  have h2 : Entails.eval a c1056 := h 1055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7691 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7689, some c7654, some c7690, some c7657, some c1114, some c1126, some c1137, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7691 : lratChecker f7691 p7691 = .success := by decide +kernel
theorem unsat7691 : Unsatisfiable (PosFin 65) f7691 := by
  apply lratCheckerSound f7691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7691
  · intro a ha; simp [p7691] at ha; subst a; trivial
  · exact checked7691
theorem derived7691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7691 := by
  apply localUnsat_implies_entails f7691 [c7689, c7654, c7690, c7657, c1114, c1126, c1137] c7691 unsat7691 (by rfl) a
  have h0 : Entails.eval a c7689 := derived7689 a h
  have h1 : Entails.eval a c7654 := derived7654 a h
  have h2 : Entails.eval a c7690 := derived7690 a h
  have h3 : Entails.eval a c7657 := derived7657 a h
  have h4 : Entails.eval a c1114 := h 1113 (by decide)
  have h5 : Entails.eval a c1126 := h 1125 (by decide)
  have h6 : Entails.eval a c1137 := h 1136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7692 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7531, some c7604, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7692 : lratChecker f7692 p7692 = .success := by decide +kernel
theorem unsat7692 : Unsatisfiable (PosFin 65) f7692 := by
  apply lratCheckerSound f7692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7692
  · intro a ha; simp [p7692] at ha; subst a; trivial
  · exact checked7692
theorem derived7692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7692 := by
  apply localUnsat_implies_entails f7692 [c7531, c7604] c7692 unsat7692 (by rfl) a
  have h0 : Entails.eval a c7531 := derived7531 a h
  have h1 : Entails.eval a c7604 := derived7604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7693 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7657, some c1534, some c1380, some c398, some c1084, some c1062, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7693 : lratChecker f7693 p7693 = .success := by decide +kernel
theorem unsat7693 : Unsatisfiable (PosFin 65) f7693 := by
  apply lratCheckerSound f7693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7693
  · intro a ha; simp [p7693] at ha; subst a; trivial
  · exact checked7693
theorem derived7693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7693 := by
  apply localUnsat_implies_entails f7693 [c7657, c1534, c1380, c398, c1084, c1062] c7693 unsat7693 (by rfl) a
  have h0 : Entails.eval a c7657 := derived7657 a h
  have h1 : Entails.eval a c1534 := h 1533 (by decide)
  have h2 : Entails.eval a c1380 := h 1379 (by decide)
  have h3 : Entails.eval a c398 := h 397 (by decide)
  have h4 : Entails.eval a c1084 := h 1083 (by decide)
  have h5 : Entails.eval a c1062 := h 1061 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7694 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c396, some c395, some c405, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7694 : lratChecker f7694 p7694 = .success := by decide +kernel
theorem unsat7694 : Unsatisfiable (PosFin 65) f7694 := by
  apply lratCheckerSound f7694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7694
  · intro a ha; simp [p7694] at ha; subst a; trivial
  · exact checked7694
theorem derived7694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7694 := by
  apply localUnsat_implies_entails f7694 [c396, c395, c405] c7694 unsat7694 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c395 := h 394 (by decide)
  have h2 : Entails.eval a c405 := h 404 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7695 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7689, some c7691, some c7692, some c7693, some c7694, some c1126, some c1125, some c1134, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7695 : lratChecker f7695 p7695 = .success := by decide +kernel
theorem unsat7695 : Unsatisfiable (PosFin 65) f7695 := by
  apply lratCheckerSound f7695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7695
  · intro a ha; simp [p7695] at ha; subst a; trivial
  · exact checked7695
theorem derived7695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7695 := by
  apply localUnsat_implies_entails f7695 [c7689, c7691, c7692, c7693, c7694, c1126, c1125, c1134] c7695 unsat7695 (by rfl) a
  have h0 : Entails.eval a c7689 := derived7689 a h
  have h1 : Entails.eval a c7691 := derived7691 a h
  have h2 : Entails.eval a c7692 := derived7692 a h
  have h3 : Entails.eval a c7693 := derived7693 a h
  have h4 : Entails.eval a c7694 := derived7694 a h
  have h5 : Entails.eval a c1126 := h 1125 (by decide)
  have h6 : Entails.eval a c1125 := h 1124 (by decide)
  have h7 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7696 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7583, some c1114, some c1112, some c1138, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7696 : lratChecker f7696 p7696 = .success := by decide +kernel
theorem unsat7696 : Unsatisfiable (PosFin 65) f7696 := by
  apply lratCheckerSound f7696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7696
  · intro a ha; simp [p7696] at ha; subst a; trivial
  · exact checked7696
theorem derived7696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7696 := by
  apply localUnsat_implies_entails f7696 [c7583, c1114, c1112, c1138] c7696 unsat7696 (by rfl) a
  have h0 : Entails.eval a c7583 := derived7583 a h
  have h1 : Entails.eval a c1114 := h 1113 (by decide)
  have h2 : Entails.eval a c1112 := h 1111 (by decide)
  have h3 : Entails.eval a c1138 := h 1137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7697 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c873, some c910, some c1357, some c1913, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7697 : lratChecker f7697 p7697 = .success := by decide +kernel
theorem unsat7697 : Unsatisfiable (PosFin 65) f7697 := by
  apply lratCheckerSound f7697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7697
  · intro a ha; simp [p7697] at ha; subst a; trivial
  · exact checked7697
theorem derived7697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7697 := by
  apply localUnsat_implies_entails f7697 [c873, c910, c1357, c1913] c7697 unsat7697 (by rfl) a
  have h0 : Entails.eval a c873 := h 872 (by decide)
  have h1 : Entails.eval a c910 := h 909 (by decide)
  have h2 : Entails.eval a c1357 := h 1356 (by decide)
  have h3 : Entails.eval a c1913 := h 1912 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7698 : DefaultClause 65 := directClause [(⟨28, by decide⟩, true), (⟨5, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c911, some c1068, some c1950, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7698 : lratChecker f7698 p7698 = .success := by decide +kernel
theorem unsat7698 : Unsatisfiable (PosFin 65) f7698 := by
  apply lratCheckerSound f7698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7698
  · intro a ha; simp [p7698] at ha; subst a; trivial
  · exact checked7698
theorem derived7698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7698 := by
  apply localUnsat_implies_entails f7698 [c911, c1068, c1950] c7698 unsat7698 (by rfl) a
  have h0 : Entails.eval a c911 := h 910 (by decide)
  have h1 : Entails.eval a c1068 := h 1067 (by decide)
  have h2 : Entails.eval a c1950 := h 1949 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7699 : DefaultClause 65 := directClause [(⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7696, some c7608, some c7680, some c7697, some c7639, some c7698, some c1134, some c7682, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7699 : lratChecker f7699 p7699 = .success := by decide +kernel
theorem unsat7699 : Unsatisfiable (PosFin 65) f7699 := by
  apply lratCheckerSound f7699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7699
  · intro a ha; simp [p7699] at ha; subst a; trivial
  · exact checked7699
theorem derived7699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7699 := by
  apply localUnsat_implies_entails f7699 [c7696, c7608, c7680, c7697, c7639, c7698, c1134, c7682] c7699 unsat7699 (by rfl) a
  have h0 : Entails.eval a c7696 := derived7696 a h
  have h1 : Entails.eval a c7608 := derived7608 a h
  have h2 : Entails.eval a c7680 := derived7680 a h
  have h3 : Entails.eval a c7697 := derived7697 a h
  have h4 : Entails.eval a c7639 := derived7639 a h
  have h5 : Entails.eval a c7698 := derived7698 a h
  have h6 : Entails.eval a c1134 := h 1133 (by decide)
  have h7 : Entails.eval a c7682 := derived7682 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7700 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7668, some c7685, some c7689, some c7695, some c7699, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7700 : lratChecker f7700 p7700 = .success := by decide +kernel
theorem unsat7700 : Unsatisfiable (PosFin 65) f7700 := by
  apply lratCheckerSound f7700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7700
  · intro a ha; simp [p7700] at ha; subst a; trivial
  · exact checked7700
theorem derived7700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7700 := by
  apply localUnsat_implies_entails f7700 [c7470, c7626, c7668, c7685, c7689, c7695, c7699] c7700 unsat7700 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7668 := derived7668 a h
  have h3 : Entails.eval a c7685 := derived7685 a h
  have h4 : Entails.eval a c7689 := derived7689 a h
  have h5 : Entails.eval a c7695 := derived7695 a h
  have h6 : Entails.eval a c7699 := derived7699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7701 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c339, some c347, some c354, some c341, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7701 : lratChecker f7701 p7701 = .success := by decide +kernel
theorem unsat7701 : Unsatisfiable (PosFin 65) f7701 := by
  apply lratCheckerSound f7701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7701
  · intro a ha; simp [p7701] at ha; subst a; trivial
  · exact checked7701
theorem derived7701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7701 := by
  apply localUnsat_implies_entails f7701 [c339, c347, c354, c341] c7701 unsat7701 (by rfl) a
  have h0 : Entails.eval a c339 := h 338 (by decide)
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7702 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7701, some c1434, some c695, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7702 : lratChecker f7702 p7702 = .success := by decide +kernel
theorem unsat7702 : Unsatisfiable (PosFin 65) f7702 := by
  apply lratCheckerSound f7702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7702
  · intro a ha; simp [p7702] at ha; subst a; trivial
  · exact checked7702
theorem derived7702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7702 := by
  apply localUnsat_implies_entails f7702 [c7701, c1434, c695] c7702 unsat7702 (by rfl) a
  have h0 : Entails.eval a c7701 := derived7701 a h
  have h1 : Entails.eval a c1434 := h 1433 (by decide)
  have h2 : Entails.eval a c695 := h 694 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7703 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1356, some c2438, some c2681, some c2204, some c2326, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p7703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7703 : lratChecker f7703 p7703 = .success := by decide +kernel
theorem unsat7703 : Unsatisfiable (PosFin 65) f7703 := by
  apply lratCheckerSound f7703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7703
  · intro a ha; simp [p7703] at ha; subst a; trivial
  · exact checked7703
theorem derived7703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7703 := by
  apply localUnsat_implies_entails f7703 [c1356, c2438, c2681, c2204, c2326] c7703 unsat7703 (by rfl) a
  have h0 : Entails.eval a c1356 := h 1355 (by decide)
  have h1 : Entails.eval a c2438 := h 2437 (by decide)
  have h2 : Entails.eval a c2681 := h 2680 (by decide)
  have h3 : Entails.eval a c2204 := h 2203 (by decide)
  have h4 : Entails.eval a c2326 := h 2325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7704 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7701, some c701, some c2027, some c2123, some c1438, some c2514, some c1441, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7704 : lratChecker f7704 p7704 = .success := by decide +kernel
theorem unsat7704 : Unsatisfiable (PosFin 65) f7704 := by
  apply lratCheckerSound f7704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7704
  · intro a ha; simp [p7704] at ha; subst a; trivial
  · exact checked7704
theorem derived7704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7704 := by
  apply localUnsat_implies_entails f7704 [c7701, c701, c2027, c2123, c1438, c2514, c1441] c7704 unsat7704 (by rfl) a
  have h0 : Entails.eval a c7701 := derived7701 a h
  have h1 : Entails.eval a c701 := h 700 (by decide)
  have h2 : Entails.eval a c2027 := h 2026 (by decide)
  have h3 : Entails.eval a c2123 := h 2122 (by decide)
  have h4 : Entails.eval a c1438 := h 1437 (by decide)
  have h5 : Entails.eval a c2514 := h 2513 (by decide)
  have h6 : Entails.eval a c1441 := h 1440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7705 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7701, some c7668, some c7559, some c7702, some c7697, some c7637, some c7703, some c7639, some c7704, some c1950, some c2120, some c1087, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7705 : lratChecker f7705 p7705 = .success := by decide +kernel
theorem unsat7705 : Unsatisfiable (PosFin 65) f7705 := by
  apply lratCheckerSound f7705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7705
  · intro a ha; simp [p7705] at ha; subst a; trivial
  · exact checked7705
theorem derived7705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7705 := by
  apply localUnsat_implies_entails f7705 [c7701, c7668, c7559, c7702, c7697, c7637, c7703, c7639, c7704, c1950, c2120, c1087] c7705 unsat7705 (by rfl) a
  have h0 : Entails.eval a c7701 := derived7701 a h
  have h1 : Entails.eval a c7668 := derived7668 a h
  have h2 : Entails.eval a c7559 := derived7559 a h
  have h3 : Entails.eval a c7702 := derived7702 a h
  have h4 : Entails.eval a c7697 := derived7697 a h
  have h5 : Entails.eval a c7637 := derived7637 a h
  have h6 : Entails.eval a c7703 := derived7703 a h
  have h7 : Entails.eval a c7639 := derived7639 a h
  have h8 : Entails.eval a c7704 := derived7704 a h
  have h9 : Entails.eval a c1950 := h 1949 (by decide)
  have h10 : Entails.eval a c2120 := h 2119 (by decide)
  have h11 : Entails.eval a c1087 := h 1086 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7706 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1164, some c2326, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7706 : lratChecker f7706 p7706 = .success := by decide +kernel
theorem unsat7706 : Unsatisfiable (PosFin 65) f7706 := by
  apply lratCheckerSound f7706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7706
  · intro a ha; simp [p7706] at ha; subst a; trivial
  · exact checked7706
theorem derived7706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7706 := by
  apply localUnsat_implies_entails f7706 [c1164, c2326] c7706 unsat7706 (by rfl) a
  have h0 : Entails.eval a c1164 := h 1163 (by decide)
  have h1 : Entails.eval a c2326 := h 2325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7707 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7706, some c2335, some c1155, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7707 : lratChecker f7707 p7707 = .success := by decide +kernel
theorem unsat7707 : Unsatisfiable (PosFin 65) f7707 := by
  apply lratCheckerSound f7707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7707
  · intro a ha; simp [p7707] at ha; subst a; trivial
  · exact checked7707
theorem derived7707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7707 := by
  apply localUnsat_implies_entails f7707 [c7706, c2335, c1155] c7707 unsat7707 (by rfl) a
  have h0 : Entails.eval a c7706 := derived7706 a h
  have h1 : Entails.eval a c2335 := h 2334 (by decide)
  have h2 : Entails.eval a c1155 := h 1154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7708 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7668, some c7701, some c7559, some c7702, some c7697, some c7637, some c7703, some c7707, some c7683, some c7705, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7708 : lratChecker f7708 p7708 = .success := by decide +kernel
theorem unsat7708 : Unsatisfiable (PosFin 65) f7708 := by
  apply lratCheckerSound f7708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7708
  · intro a ha; simp [p7708] at ha; subst a; trivial
  · exact checked7708
theorem derived7708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7708 := by
  apply localUnsat_implies_entails f7708 [c7668, c7701, c7559, c7702, c7697, c7637, c7703, c7707, c7683, c7705] c7708 unsat7708 (by rfl) a
  have h0 : Entails.eval a c7668 := derived7668 a h
  have h1 : Entails.eval a c7701 := derived7701 a h
  have h2 : Entails.eval a c7559 := derived7559 a h
  have h3 : Entails.eval a c7702 := derived7702 a h
  have h4 : Entails.eval a c7697 := derived7697 a h
  have h5 : Entails.eval a c7637 := derived7637 a h
  have h6 : Entails.eval a c7703 := derived7703 a h
  have h7 : Entails.eval a c7707 := derived7707 a h
  have h8 : Entails.eval a c7683 := derived7683 a h
  have h9 : Entails.eval a c7705 := derived7705 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7709 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7650, some c7663, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7709 : lratChecker f7709 p7709 = .success := by decide +kernel
theorem unsat7709 : Unsatisfiable (PosFin 65) f7709 := by
  apply lratCheckerSound f7709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7709
  · intro a ha; simp [p7709] at ha; subst a; trivial
  · exact checked7709
theorem derived7709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7709 := by
  apply localUnsat_implies_entails f7709 [c7650, c7663] c7709 unsat7709 (by rfl) a
  have h0 : Entails.eval a c7650 := derived7650 a h
  have h1 : Entails.eval a c7663 := derived7663 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7710 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1292, some c1358, some c1434, some c1965, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7710 : lratChecker f7710 p7710 = .success := by decide +kernel
theorem unsat7710 : Unsatisfiable (PosFin 65) f7710 := by
  apply lratCheckerSound f7710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7710
  · intro a ha; simp [p7710] at ha; subst a; trivial
  · exact checked7710
theorem derived7710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7710 := by
  apply localUnsat_implies_entails f7710 [c1292, c1358, c1434, c1965] c7710 unsat7710 (by rfl) a
  have h0 : Entails.eval a c1292 := h 1291 (by decide)
  have h1 : Entails.eval a c1358 := h 1357 (by decide)
  have h2 : Entails.eval a c1434 := h 1433 (by decide)
  have h3 : Entails.eval a c1965 := h 1964 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7711 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1287, some c1352, some c1992, some c1900, some c1026, some c1018, some c1028, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7711 : lratChecker f7711 p7711 = .success := by decide +kernel
theorem unsat7711 : Unsatisfiable (PosFin 65) f7711 := by
  apply lratCheckerSound f7711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7711
  · intro a ha; simp [p7711] at ha; subst a; trivial
  · exact checked7711
theorem derived7711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7711 := by
  apply localUnsat_implies_entails f7711 [c1287, c1352, c1992, c1900, c1026, c1018, c1028] c7711 unsat7711 (by rfl) a
  have h0 : Entails.eval a c1287 := h 1286 (by decide)
  have h1 : Entails.eval a c1352 := h 1351 (by decide)
  have h2 : Entails.eval a c1992 := h 1991 (by decide)
  have h3 : Entails.eval a c1900 := h 1899 (by decide)
  have h4 : Entails.eval a c1026 := h 1025 (by decide)
  have h5 : Entails.eval a c1018 := h 1017 (by decide)
  have h6 : Entails.eval a c1028 := h 1027 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7712 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7379, some c1066, some c1122, some c2029, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7712 : lratChecker f7712 p7712 = .success := by decide +kernel
theorem unsat7712 : Unsatisfiable (PosFin 65) f7712 := by
  apply lratCheckerSound f7712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7712
  · intro a ha; simp [p7712] at ha; subst a; trivial
  · exact checked7712
theorem derived7712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7712 := by
  apply localUnsat_implies_entails f7712 [c7379, c1066, c1122, c2029] c7712 unsat7712 (by rfl) a
  have h0 : Entails.eval a c7379 := derived7379 a h
  have h1 : Entails.eval a c1066 := h 1065 (by decide)
  have h2 : Entails.eval a c1122 := h 1121 (by decide)
  have h3 : Entails.eval a c2029 := h 2028 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7713 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7608, some c7711, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7713 : lratChecker f7713 p7713 = .success := by decide +kernel
theorem unsat7713 : Unsatisfiable (PosFin 65) f7713 := by
  apply lratCheckerSound f7713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7713
  · intro a ha; simp [p7713] at ha; subst a; trivial
  · exact checked7713
theorem derived7713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7713 := by
  apply localUnsat_implies_entails f7713 [c7608, c7711] c7713 unsat7713 (by rfl) a
  have h0 : Entails.eval a c7608 := derived7608 a h
  have h1 : Entails.eval a c7711 := derived7711 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7714 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7626, some c7470, some c7668, some c7700, some c7708, some c7709, some c7710, some c7713, some c7697, some c7712, some c7639, some c7698, some c1140, some c743, some c2027, some c2123, some c7682, some c1438, some c2514, some c1441, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7714 : lratChecker f7714 p7714 = .success := by decide +kernel
theorem unsat7714 : Unsatisfiable (PosFin 65) f7714 := by
  apply lratCheckerSound f7714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7714
  · intro a ha; simp [p7714] at ha; subst a; trivial
  · exact checked7714
theorem derived7714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7714 := by
  apply localUnsat_implies_entails f7714 [c7626, c7470, c7668, c7700, c7708, c7709, c7710, c7713, c7697, c7712, c7639, c7698, c1140, c743, c2027, c2123, c7682, c1438, c2514, c1441] c7714 unsat7714 (by rfl) a
  have h0 : Entails.eval a c7626 := derived7626 a h
  have h1 : Entails.eval a c7470 := derived7470 a h
  have h2 : Entails.eval a c7668 := derived7668 a h
  have h3 : Entails.eval a c7700 := derived7700 a h
  have h4 : Entails.eval a c7708 := derived7708 a h
  have h5 : Entails.eval a c7709 := derived7709 a h
  have h6 : Entails.eval a c7710 := derived7710 a h
  have h7 : Entails.eval a c7713 := derived7713 a h
  have h8 : Entails.eval a c7697 := derived7697 a h
  have h9 : Entails.eval a c7712 := derived7712 a h
  have h10 : Entails.eval a c7639 := derived7639 a h
  have h11 : Entails.eval a c7698 := derived7698 a h
  have h12 : Entails.eval a c1140 := h 1139 (by decide)
  have h13 : Entails.eval a c743 := h 742 (by decide)
  have h14 : Entails.eval a c2027 := h 2026 (by decide)
  have h15 : Entails.eval a c2123 := h 2122 (by decide)
  have h16 : Entails.eval a c7682 := derived7682 a h
  have h17 : Entails.eval a c1438 := h 1437 (by decide)
  have h18 : Entails.eval a c2514 := h 2513 (by decide)
  have h19 : Entails.eval a c1441 := h 1440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7715 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2284, some c1511, some c1024, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7715 : lratChecker f7715 p7715 = .success := by decide +kernel
theorem unsat7715 : Unsatisfiable (PosFin 65) f7715 := by
  apply lratCheckerSound f7715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7715
  · intro a ha; simp [p7715] at ha; subst a; trivial
  · exact checked7715
theorem derived7715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7715 := by
  apply localUnsat_implies_entails f7715 [c2284, c1511, c1024] c7715 unsat7715 (by rfl) a
  have h0 : Entails.eval a c2284 := h 2283 (by decide)
  have h1 : Entails.eval a c1511 := h 1510 (by decide)
  have h2 : Entails.eval a c1024 := h 1023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7716 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1001, some c1008, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7716 : lratChecker f7716 p7716 = .success := by decide +kernel
theorem unsat7716 : Unsatisfiable (PosFin 65) f7716 := by
  apply lratCheckerSound f7716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7716
  · intro a ha; simp [p7716] at ha; subst a; trivial
  · exact checked7716
theorem derived7716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7716 := by
  apply localUnsat_implies_entails f7716 [c1001, c1008] c7716 unsat7716 (by rfl) a
  have h0 : Entails.eval a c1001 := h 1000 (by decide)
  have h1 : Entails.eval a c1008 := h 1007 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7717 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1080, some c1093, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7717 : lratChecker f7717 p7717 = .success := by decide +kernel
theorem unsat7717 : Unsatisfiable (PosFin 65) f7717 := by
  apply lratCheckerSound f7717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7717
  · intro a ha; simp [p7717] at ha; subst a; trivial
  · exact checked7717
theorem derived7717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7717 := by
  apply localUnsat_implies_entails f7717 [c1080, c1093] c7717 unsat7717 (by rfl) a
  have h0 : Entails.eval a c1080 := h 1079 (by decide)
  have h1 : Entails.eval a c1093 := h 1092 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7718 : DefaultClause 65 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2230, some c2238, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7718 : lratChecker f7718 p7718 = .success := by decide +kernel
theorem unsat7718 : Unsatisfiable (PosFin 65) f7718 := by
  apply lratCheckerSound f7718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7718
  · intro a ha; simp [p7718] at ha; subst a; trivial
  · exact checked7718
theorem derived7718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7718 := by
  apply localUnsat_implies_entails f7718 [c2230, c2238] c7718 unsat7718 (by rfl) a
  have h0 : Entails.eval a c2230 := h 2229 (by decide)
  have h1 : Entails.eval a c2238 := h 2237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7719 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨30, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c41, some c37, some c38, some c34, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7719 : lratChecker f7719 p7719 = .success := by decide +kernel
theorem unsat7719 : Unsatisfiable (PosFin 65) f7719 := by
  apply lratCheckerSound f7719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7719
  · intro a ha; simp [p7719] at ha; subst a; trivial
  · exact checked7719
theorem derived7719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7719 := by
  apply localUnsat_implies_entails f7719 [c41, c37, c38, c34] c7719 unsat7719 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7720 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7626, some c7470, some c310, some c1674, some c1147, some c7719, some c55, some c56, some c6694, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7720 : lratChecker f7720 p7720 = .success := by decide +kernel
theorem unsat7720 : Unsatisfiable (PosFin 65) f7720 := by
  apply lratCheckerSound f7720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7720
  · intro a ha; simp [p7720] at ha; subst a; trivial
  · exact checked7720
theorem derived7720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7720 := by
  apply localUnsat_implies_entails f7720 [c7626, c7470, c310, c1674, c1147, c7719, c55, c56, c6694] c7720 unsat7720 (by rfl) a
  have h0 : Entails.eval a c7626 := derived7626 a h
  have h1 : Entails.eval a c7470 := derived7470 a h
  have h2 : Entails.eval a c310 := h 309 (by decide)
  have h3 : Entails.eval a c1674 := h 1673 (by decide)
  have h4 : Entails.eval a c1147 := h 1146 (by decide)
  have h5 : Entails.eval a c7719 := derived7719 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c6694 := derived6694 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7721 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c7626, some c7470, some c7627, some c7629, some c7656, some c7501, some c780, some c770, some c764, some c759, some c332, some c357, some c768, some c7715, some c7716, some c7718, some c7717, some c7720, some c298, some c1685, some c1151, some c7719, some c55, some c56, some c6694, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked7721 : lratChecker f7721 p7721 = .success := by decide +kernel
theorem unsat7721 : Unsatisfiable (PosFin 65) f7721 := by
  apply lratCheckerSound f7721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7721
  · intro a ha; simp [p7721] at ha; subst a; trivial
  · exact checked7721
theorem derived7721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7721 := by
  apply localUnsat_implies_entails f7721 [c7714, c7626, c7470, c7627, c7629, c7656, c7501, c780, c770, c764, c759, c332, c357, c768, c7715, c7716, c7718, c7717, c7720, c298, c1685, c1151, c7719, c55, c56, c6694] c7721 unsat7721 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7470 := derived7470 a h
  have h3 : Entails.eval a c7627 := derived7627 a h
  have h4 : Entails.eval a c7629 := derived7629 a h
  have h5 : Entails.eval a c7656 := derived7656 a h
  have h6 : Entails.eval a c7501 := derived7501 a h
  have h7 : Entails.eval a c780 := h 779 (by decide)
  have h8 : Entails.eval a c770 := h 769 (by decide)
  have h9 : Entails.eval a c764 := h 763 (by decide)
  have h10 : Entails.eval a c759 := h 758 (by decide)
  have h11 : Entails.eval a c332 := h 331 (by decide)
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c768 := h 767 (by decide)
  have h14 : Entails.eval a c7715 := derived7715 a h
  have h15 : Entails.eval a c7716 := derived7716 a h
  have h16 : Entails.eval a c7718 := derived7718 a h
  have h17 : Entails.eval a c7717 := derived7717 a h
  have h18 : Entails.eval a c7720 := derived7720 a h
  have h19 : Entails.eval a c298 := h 297 (by decide)
  have h20 : Entails.eval a c1685 := h 1684 (by decide)
  have h21 : Entails.eval a c1151 := h 1150 (by decide)
  have h22 : Entails.eval a c7719 := derived7719 a h
  have h23 : Entails.eval a c55 := h 54 (by decide)
  have h24 : Entails.eval a c56 := h 55 (by decide)
  have h25 : Entails.eval a c6694 := derived6694 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7722 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7570, some c7672, some c355, some c7331, some c1474, some c1148, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7722 : lratChecker f7722 p7722 = .success := by decide +kernel
theorem unsat7722 : Unsatisfiable (PosFin 65) f7722 := by
  apply lratCheckerSound f7722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7722
  · intro a ha; simp [p7722] at ha; subst a; trivial
  · exact checked7722
theorem derived7722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7722 := by
  apply localUnsat_implies_entails f7722 [c7570, c7672, c355, c7331, c1474, c1148] c7722 unsat7722 (by rfl) a
  have h0 : Entails.eval a c7570 := derived7570 a h
  have h1 : Entails.eval a c7672 := derived7672 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c7331 := derived7331 a h
  have h4 : Entails.eval a c1474 := h 1473 (by decide)
  have h5 : Entails.eval a c1148 := h 1147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7723 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1509, some c1472, some c2596, some c2671, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p7723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7723 : lratChecker f7723 p7723 = .success := by decide +kernel
theorem unsat7723 : Unsatisfiable (PosFin 65) f7723 := by
  apply lratCheckerSound f7723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7723
  · intro a ha; simp [p7723] at ha; subst a; trivial
  · exact checked7723
theorem derived7723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7723 := by
  apply localUnsat_implies_entails f7723 [c1509, c1472, c2596, c2671] c7723 unsat7723 (by rfl) a
  have h0 : Entails.eval a c1509 := h 1508 (by decide)
  have h1 : Entails.eval a c1472 := h 1471 (by decide)
  have h2 : Entails.eval a c2596 := h 2595 (by decide)
  have h3 : Entails.eval a c2671 := h 2670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7724 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨8, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2658, some c2509, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7724 : lratChecker f7724 p7724 = .success := by decide +kernel
theorem unsat7724 : Unsatisfiable (PosFin 65) f7724 := by
  apply lratCheckerSound f7724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7724
  · intro a ha; simp [p7724] at ha; subst a; trivial
  · exact checked7724
theorem derived7724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7724 := by
  apply localUnsat_implies_entails f7724 [c2658, c2509] c7724 unsat7724 (by rfl) a
  have h0 : Entails.eval a c2658 := h 2657 (by decide)
  have h1 : Entails.eval a c2509 := h 2508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7725 : DefaultClause 65 := directClause [(⟨8, by decide⟩, true), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7724, some c1760, some c1870, some c2506, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7725 : lratChecker f7725 p7725 = .success := by decide +kernel
theorem unsat7725 : Unsatisfiable (PosFin 65) f7725 := by
  apply lratCheckerSound f7725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7725
  · intro a ha; simp [p7725] at ha; subst a; trivial
  · exact checked7725
theorem derived7725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7725 := by
  apply localUnsat_implies_entails f7725 [c7724, c1760, c1870, c2506] c7725 unsat7725 (by rfl) a
  have h0 : Entails.eval a c7724 := derived7724 a h
  have h1 : Entails.eval a c1760 := h 1759 (by decide)
  have h2 : Entails.eval a c1870 := h 1869 (by decide)
  have h3 : Entails.eval a c2506 := h 2505 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7726 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c328, some c327, some c6692, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p7726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7726 : lratChecker f7726 p7726 = .success := by decide +kernel
theorem unsat7726 : Unsatisfiable (PosFin 65) f7726 := by
  apply lratCheckerSound f7726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7726
  · intro a ha; simp [p7726] at ha; subst a; trivial
  · exact checked7726
theorem derived7726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7726 := by
  apply localUnsat_implies_entails f7726 [c328, c327, c6692] c7726 unsat7726 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c6692 := derived6692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7727 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, false), (⟨26, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7626, some c2028, some c1769, some c2134, some c7719, some c7726, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7727 : lratChecker f7727 p7727 = .success := by decide +kernel
theorem unsat7727 : Unsatisfiable (PosFin 65) f7727 := by
  apply lratCheckerSound f7727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7727
  · intro a ha; simp [p7727] at ha; subst a; trivial
  · exact checked7727
theorem derived7727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7727 := by
  apply localUnsat_implies_entails f7727 [c7626, c2028, c1769, c2134, c7719, c7726] c7727 unsat7727 (by rfl) a
  have h0 : Entails.eval a c7626 := derived7626 a h
  have h1 : Entails.eval a c2028 := h 2027 (by decide)
  have h2 : Entails.eval a c1769 := h 1768 (by decide)
  have h3 : Entails.eval a c2134 := h 2133 (by decide)
  have h4 : Entails.eval a c7719 := derived7719 a h
  have h5 : Entails.eval a c7726 := derived7726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7728 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c359, some c7626, some c368, some c7714, some c7721, some c7470, some c7722, some c7676, some c7723, some c362, some c364, some c352, some c332, some c380, some c412, some c7590, some c7725, some c7727, some c1760, some c2434, some c2474, some c7726, some c1273, some c1406, some c1407, some c3177, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked7728 : lratChecker f7728 p7728 = .success := by decide +kernel
theorem unsat7728 : Unsatisfiable (PosFin 65) f7728 := by
  apply lratCheckerSound f7728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7728
  · intro a ha; simp [p7728] at ha; subst a; trivial
  · exact checked7728
theorem derived7728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7728 := by
  apply localUnsat_implies_entails f7728 [c359, c7626, c368, c7714, c7721, c7470, c7722, c7676, c7723, c362, c364, c352, c332, c380, c412, c7590, c7725, c7727, c1760, c2434, c2474, c7726, c1273, c1406, c1407, c3177] c7728 unsat7728 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c7714 := derived7714 a h
  have h4 : Entails.eval a c7721 := derived7721 a h
  have h5 : Entails.eval a c7470 := derived7470 a h
  have h6 : Entails.eval a c7722 := derived7722 a h
  have h7 : Entails.eval a c7676 := derived7676 a h
  have h8 : Entails.eval a c7723 := derived7723 a h
  have h9 : Entails.eval a c362 := h 361 (by decide)
  have h10 : Entails.eval a c364 := h 363 (by decide)
  have h11 : Entails.eval a c352 := h 351 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c412 := h 411 (by decide)
  have h15 : Entails.eval a c7590 := derived7590 a h
  have h16 : Entails.eval a c7725 := derived7725 a h
  have h17 : Entails.eval a c7727 := derived7727 a h
  have h18 : Entails.eval a c1760 := h 1759 (by decide)
  have h19 : Entails.eval a c2434 := h 2433 (by decide)
  have h20 : Entails.eval a c2474 := h 2473 (by decide)
  have h21 : Entails.eval a c7726 := derived7726 a h
  have h22 : Entails.eval a c1273 := h 1272 (by decide)
  have h23 : Entails.eval a c1406 := h 1405 (by decide)
  have h24 : Entails.eval a c1407 := h 1406 (by decide)
  have h25 : Entails.eval a c3177 := h 3176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7729 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨10, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c999, some c1144, some c2327, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7729 : lratChecker f7729 p7729 = .success := by decide +kernel
theorem unsat7729 : Unsatisfiable (PosFin 65) f7729 := by
  apply lratCheckerSound f7729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7729
  · intro a ha; simp [p7729] at ha; subst a; trivial
  · exact checked7729
theorem derived7729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7729 := by
  apply localUnsat_implies_entails f7729 [c999, c1144, c2327] c7729 unsat7729 (by rfl) a
  have h0 : Entails.eval a c999 := h 998 (by decide)
  have h1 : Entails.eval a c1144 := h 1143 (by decide)
  have h2 : Entails.eval a c2327 := h 2326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7730 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7626, some c359, some c368, some c352, some c7470, some c7714, some c7722, some c7728, some c7729, some c1149, some c1004, some c2333, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7730 : lratChecker f7730 p7730 = .success := by decide +kernel
theorem unsat7730 : Unsatisfiable (PosFin 65) f7730 := by
  apply lratCheckerSound f7730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7730
  · intro a ha; simp [p7730] at ha; subst a; trivial
  · exact checked7730
theorem derived7730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7730 := by
  apply localUnsat_implies_entails f7730 [c7626, c359, c368, c352, c7470, c7714, c7722, c7728, c7729, c1149, c1004, c2333] c7730 unsat7730 (by rfl) a
  have h0 : Entails.eval a c7626 := derived7626 a h
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c7470 := derived7470 a h
  have h5 : Entails.eval a c7714 := derived7714 a h
  have h6 : Entails.eval a c7722 := derived7722 a h
  have h7 : Entails.eval a c7728 := derived7728 a h
  have h8 : Entails.eval a c7729 := derived7729 a h
  have h9 : Entails.eval a c1149 := h 1148 (by decide)
  have h10 : Entails.eval a c1004 := h 1003 (by decide)
  have h11 : Entails.eval a c2333 := h 2332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7731 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7714, some c7722, some c7721, some c359, some c7730, some c342, some c1509, some c1472, some c2676, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7731 : lratChecker f7731 p7731 = .success := by decide +kernel
theorem unsat7731 : Unsatisfiable (PosFin 65) f7731 := by
  apply lratCheckerSound f7731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7731
  · intro a ha; simp [p7731] at ha; subst a; trivial
  · exact checked7731
theorem derived7731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7731 := by
  apply localUnsat_implies_entails f7731 [c7470, c7714, c7722, c7721, c359, c7730, c342, c1509, c1472, c2676] c7731 unsat7731 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7714 := derived7714 a h
  have h2 : Entails.eval a c7722 := derived7722 a h
  have h3 : Entails.eval a c7721 := derived7721 a h
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c7730 := derived7730 a h
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c1509 := h 1508 (by decide)
  have h8 : Entails.eval a c1472 := h 1471 (by decide)
  have h9 : Entails.eval a c2676 := h 2675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7732 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7331, some c418, some c361, some c409, some c352, some c332, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7732 : lratChecker f7732 p7732 = .success := by decide +kernel
theorem unsat7732 : Unsatisfiable (PosFin 65) f7732 := by
  apply lratCheckerSound f7732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7732
  · intro a ha; simp [p7732] at ha; subst a; trivial
  · exact checked7732
theorem derived7732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7732 := by
  apply localUnsat_implies_entails f7732 [c7331, c418, c361, c409, c352, c332] c7732 unsat7732 (by rfl) a
  have h0 : Entails.eval a c7331 := derived7331 a h
  have h1 : Entails.eval a c418 := h 417 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c409 := h 408 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7733 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7722, some c348, some c7732, some c7729, some c1150, some c1007, some c2333, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7733 : lratChecker f7733 p7733 = .success := by decide +kernel
theorem unsat7733 : Unsatisfiable (PosFin 65) f7733 := by
  apply lratCheckerSound f7733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7733
  · intro a ha; simp [p7733] at ha; subst a; trivial
  · exact checked7733
theorem derived7733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7733 := by
  apply localUnsat_implies_entails f7733 [c7722, c348, c7732, c7729, c1150, c1007, c2333] c7733 unsat7733 (by rfl) a
  have h0 : Entails.eval a c7722 := derived7722 a h
  have h1 : Entails.eval a c348 := h 347 (by decide)
  have h2 : Entails.eval a c7732 := derived7732 a h
  have h3 : Entails.eval a c7729 := derived7729 a h
  have h4 : Entails.eval a c1150 := h 1149 (by decide)
  have h5 : Entails.eval a c1007 := h 1006 (by decide)
  have h6 : Entails.eval a c2333 := h 2332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7734 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7331, some c7732, some c361, some c368, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7734 : lratChecker f7734 p7734 = .success := by decide +kernel
theorem unsat7734 : Unsatisfiable (PosFin 65) f7734 := by
  apply lratCheckerSound f7734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7734
  · intro a ha; simp [p7734] at ha; subst a; trivial
  · exact checked7734
theorem derived7734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7734 := by
  apply localUnsat_implies_entails f7734 [c7331, c7732, c361, c368] c7734 unsat7734 (by rfl) a
  have h0 : Entails.eval a c7331 := derived7331 a h
  have h1 : Entails.eval a c7732 := derived7732 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7735 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1509, some c1472, some c2676, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7735 : lratChecker f7735 p7735 = .success := by decide +kernel
theorem unsat7735 : Unsatisfiable (PosFin 65) f7735 := by
  apply lratCheckerSound f7735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7735
  · intro a ha; simp [p7735] at ha; subst a; trivial
  · exact checked7735
theorem derived7735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7735 := by
  apply localUnsat_implies_entails f7735 [c1509, c1472, c2676] c7735 unsat7735 (by rfl) a
  have h0 : Entails.eval a c1509 := h 1508 (by decide)
  have h1 : Entails.eval a c1472 := h 1471 (by decide)
  have h2 : Entails.eval a c2676 := h 2675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7736 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1162, some c2683, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7736 : lratChecker f7736 p7736 = .success := by decide +kernel
theorem unsat7736 : Unsatisfiable (PosFin 65) f7736 := by
  apply lratCheckerSound f7736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7736
  · intro a ha; simp [p7736] at ha; subst a; trivial
  · exact checked7736
theorem derived7736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7736 := by
  apply localUnsat_implies_entails f7736 [c1162, c2683] c7736 unsat7736 (by rfl) a
  have h0 : Entails.eval a c1162 := h 1161 (by decide)
  have h1 : Entails.eval a c2683 := h 2682 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7737 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7717, some c7736, some c1393, some c1400, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7737 : lratChecker f7737 p7737 = .success := by decide +kernel
theorem unsat7737 : Unsatisfiable (PosFin 65) f7737 := by
  apply lratCheckerSound f7737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7737
  · intro a ha; simp [p7737] at ha; subst a; trivial
  · exact checked7737
theorem derived7737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7737 := by
  apply localUnsat_implies_entails f7737 [c7717, c7736, c1393, c1400] c7737 unsat7737 (by rfl) a
  have h0 : Entails.eval a c7717 := derived7717 a h
  have h1 : Entails.eval a c7736 := derived7736 a h
  have h2 : Entails.eval a c1393 := h 1392 (by decide)
  have h3 : Entails.eval a c1400 := h 1399 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7738 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1162, some c1165, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7738 : lratChecker f7738 p7738 = .success := by decide +kernel
theorem unsat7738 : Unsatisfiable (PosFin 65) f7738 := by
  apply lratCheckerSound f7738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7738
  · intro a ha; simp [p7738] at ha; subst a; trivial
  · exact checked7738
theorem derived7738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7738 := by
  apply localUnsat_implies_entails f7738 [c1162, c1165] c7738 unsat7738 (by rfl) a
  have h0 : Entails.eval a c1162 := h 1161 (by decide)
  have h1 : Entails.eval a c1165 := h 1164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7739 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c372, some c371, some c6694, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7739 : lratChecker f7739 p7739 = .success := by decide +kernel
theorem unsat7739 : Unsatisfiable (PosFin 65) f7739 := by
  apply lratCheckerSound f7739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7739
  · intro a ha; simp [p7739] at ha; subst a; trivial
  · exact checked7739
theorem derived7739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7739 := by
  apply localUnsat_implies_entails f7739 [c372, c371, c6694] c7739 unsat7739 (by rfl) a
  have h0 : Entails.eval a c372 := h 371 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c6694 := derived6694 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7740 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨59, by decide⟩, true), (⟨22, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7734, some c7733, some c7722, some c7735, some c361, some c338, some c355, some c349, some c357, some c7716, some c7737, some c7738, some c2321, some c7719, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7740 : lratChecker f7740 p7740 = .success := by decide +kernel
theorem unsat7740 : Unsatisfiable (PosFin 65) f7740 := by
  apply lratCheckerSound f7740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7740
  · intro a ha; simp [p7740] at ha; subst a; trivial
  · exact checked7740
theorem derived7740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7740 := by
  apply localUnsat_implies_entails f7740 [c7734, c7733, c7722, c7735, c361, c338, c355, c349, c357, c7716, c7737, c7738, c2321, c7719] c7740 unsat7740 (by rfl) a
  have h0 : Entails.eval a c7734 := derived7734 a h
  have h1 : Entails.eval a c7733 := derived7733 a h
  have h2 : Entails.eval a c7722 := derived7722 a h
  have h3 : Entails.eval a c7735 := derived7735 a h
  have h4 : Entails.eval a c361 := h 360 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c7716 := derived7716 a h
  have h10 : Entails.eval a c7737 := derived7737 a h
  have h11 : Entails.eval a c7738 := derived7738 a h
  have h12 : Entails.eval a c2321 := h 2320 (by decide)
  have h13 : Entails.eval a c7719 := derived7719 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7741 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c7626, some c7470, some c7721, some c7731, some c7733, some c7739, some c7740, some c345, some c346, some c356, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7741 : lratChecker f7741 p7741 = .success := by decide +kernel
theorem unsat7741 : Unsatisfiable (PosFin 65) f7741 := by
  apply lratCheckerSound f7741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7741
  · intro a ha; simp [p7741] at ha; subst a; trivial
  · exact checked7741
theorem derived7741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7741 := by
  apply localUnsat_implies_entails f7741 [c7714, c7626, c7470, c7721, c7731, c7733, c7739, c7740, c345, c346, c356] c7741 unsat7741 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7470 := derived7470 a h
  have h3 : Entails.eval a c7721 := derived7721 a h
  have h4 : Entails.eval a c7731 := derived7731 a h
  have h5 : Entails.eval a c7733 := derived7733 a h
  have h6 : Entails.eval a c7739 := derived7739 a h
  have h7 : Entails.eval a c7740 := derived7740 a h
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7742 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1345, some c2424, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7742 : lratChecker f7742 p7742 = .success := by decide +kernel
theorem unsat7742 : Unsatisfiable (PosFin 65) f7742 := by
  apply lratCheckerSound f7742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7742
  · intro a ha; simp [p7742] at ha; subst a; trivial
  · exact checked7742
theorem derived7742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7742 := by
  apply localUnsat_implies_entails f7742 [c1345, c2424] c7742 unsat7742 (by rfl) a
  have h0 : Entails.eval a c1345 := h 1344 (by decide)
  have h1 : Entails.eval a c2424 := h 2423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7743 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2103, some c2134, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7743 : lratChecker f7743 p7743 = .success := by decide +kernel
theorem unsat7743 : Unsatisfiable (PosFin 65) f7743 := by
  apply lratCheckerSound f7743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7743
  · intro a ha; simp [p7743] at ha; subst a; trivial
  · exact checked7743
theorem derived7743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7743 := by
  apply localUnsat_implies_entails f7743 [c2103, c2134] c7743 unsat7743 (by rfl) a
  have h0 : Entails.eval a c2103 := h 2102 (by decide)
  have h1 : Entails.eval a c2134 := h 2133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7744 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, false), (⟨31, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7743, some c2117, some c2133, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7744 : lratChecker f7744 p7744 = .success := by decide +kernel
theorem unsat7744 : Unsatisfiable (PosFin 65) f7744 := by
  apply lratCheckerSound f7744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7744
  · intro a ha; simp [p7744] at ha; subst a; trivial
  · exact checked7744
theorem derived7744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7744 := by
  apply localUnsat_implies_entails f7744 [c7743, c2117, c2133] c7744 unsat7744 (by rfl) a
  have h0 : Entails.eval a c7743 := derived7743 a h
  have h1 : Entails.eval a c2117 := h 2116 (by decide)
  have h2 : Entails.eval a c2133 := h 2132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7745 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c13, some c2911, some c1452, some c22, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7745 : lratChecker f7745 p7745 = .success := by decide +kernel
theorem unsat7745 : Unsatisfiable (PosFin 65) f7745 := by
  apply lratCheckerSound f7745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7745
  · intro a ha; simp [p7745] at ha; subst a; trivial
  · exact checked7745
theorem derived7745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7745 := by
  apply localUnsat_implies_entails f7745 [c13, c2911, c1452, c22] c7745 unsat7745 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c2911 := h 2910 (by decide)
  have h2 : Entails.eval a c1452 := h 1451 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7746 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c7626, some c1437, some c1421, some c7470, some c1769, some c2240, some c7745, some c897, some c49, some c6675, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7746 : lratChecker f7746 p7746 = .success := by decide +kernel
theorem unsat7746 : Unsatisfiable (PosFin 65) f7746 := by
  apply lratCheckerSound f7746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7746
  · intro a ha; simp [p7746] at ha; subst a; trivial
  · exact checked7746
theorem derived7746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7746 := by
  apply localUnsat_implies_entails f7746 [c7714, c7626, c1437, c1421, c7470, c1769, c2240, c7745, c897, c49, c6675] c7746 unsat7746 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c1437 := h 1436 (by decide)
  have h3 : Entails.eval a c1421 := h 1420 (by decide)
  have h4 : Entails.eval a c7470 := derived7470 a h
  have h5 : Entails.eval a c1769 := h 1768 (by decide)
  have h6 : Entails.eval a c2240 := h 2239 (by decide)
  have h7 : Entails.eval a c7745 := derived7745 a h
  have h8 : Entails.eval a c897 := h 896 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c6675 := derived6675 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7747 : DefaultClause 65 := directClause [(⟨59, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3148, some c1452, some c1453, some c22, some (DefaultClause.unit (⟨59, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7747 : lratChecker f7747 p7747 = .success := by decide +kernel
theorem unsat7747 : Unsatisfiable (PosFin 65) f7747 := by
  apply lratCheckerSound f7747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7747
  · intro a ha; simp [p7747] at ha; subst a; trivial
  · exact checked7747
theorem derived7747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7747 := by
  apply localUnsat_implies_entails f7747 [c3148, c1452, c1453, c22] c7747 unsat7747 (by rfl) a
  have h0 : Entails.eval a c3148 := h 3147 (by decide)
  have h1 : Entails.eval a c1452 := h 1451 (by decide)
  have h2 : Entails.eval a c1453 := h 1452 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7748 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7626, some c1450, some c1449, some c1444, some c7590, some c1437, some c7714, some c7725, some c7744, some c7746, some c7747, some c110, some c165, some c6740, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7748 : lratChecker f7748 p7748 = .success := by decide +kernel
theorem unsat7748 : Unsatisfiable (PosFin 65) f7748 := by
  apply lratCheckerSound f7748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7748
  · intro a ha; simp [p7748] at ha; subst a; trivial
  · exact checked7748
theorem derived7748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7748 := by
  apply localUnsat_implies_entails f7748 [c7626, c1450, c1449, c1444, c7590, c1437, c7714, c7725, c7744, c7746, c7747, c110, c165, c6740] c7748 unsat7748 (by rfl) a
  have h0 : Entails.eval a c7626 := derived7626 a h
  have h1 : Entails.eval a c1450 := h 1449 (by decide)
  have h2 : Entails.eval a c1449 := h 1448 (by decide)
  have h3 : Entails.eval a c1444 := h 1443 (by decide)
  have h4 : Entails.eval a c7590 := derived7590 a h
  have h5 : Entails.eval a c1437 := h 1436 (by decide)
  have h6 : Entails.eval a c7714 := derived7714 a h
  have h7 : Entails.eval a c7725 := derived7725 a h
  have h8 : Entails.eval a c7744 := derived7744 a h
  have h9 : Entails.eval a c7746 := derived7746 a h
  have h10 : Entails.eval a c7747 := derived7747 a h
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c6740 := derived6740 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7749 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7741, some c7626, some c7627, some c7714, some c7355, some c7670, some c7676, some c1450, some c1449, some c1444, some c7590, some c7742, some c7470, some c7748, some c7729, some c1150, some c1007, some c2333, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked7749 : lratChecker f7749 p7749 = .success := by decide +kernel
theorem unsat7749 : Unsatisfiable (PosFin 65) f7749 := by
  apply lratCheckerSound f7749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7749
  · intro a ha; simp [p7749] at ha; subst a; trivial
  · exact checked7749
theorem derived7749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7749 := by
  apply localUnsat_implies_entails f7749 [c7741, c7626, c7627, c7714, c7355, c7670, c7676, c1450, c1449, c1444, c7590, c7742, c7470, c7748, c7729, c1150, c1007, c2333] c7749 unsat7749 (by rfl) a
  have h0 : Entails.eval a c7741 := derived7741 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7627 := derived7627 a h
  have h3 : Entails.eval a c7714 := derived7714 a h
  have h4 : Entails.eval a c7355 := derived7355 a h
  have h5 : Entails.eval a c7670 := derived7670 a h
  have h6 : Entails.eval a c7676 := derived7676 a h
  have h7 : Entails.eval a c1450 := h 1449 (by decide)
  have h8 : Entails.eval a c1449 := h 1448 (by decide)
  have h9 : Entails.eval a c1444 := h 1443 (by decide)
  have h10 : Entails.eval a c7590 := derived7590 a h
  have h11 : Entails.eval a c7742 := derived7742 a h
  have h12 : Entails.eval a c7470 := derived7470 a h
  have h13 : Entails.eval a c7748 := derived7748 a h
  have h14 : Entails.eval a c7729 := derived7729 a h
  have h15 : Entails.eval a c1150 := h 1149 (by decide)
  have h16 : Entails.eval a c1007 := h 1006 (by decide)
  have h17 : Entails.eval a c2333 := h 2332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7750 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7741, some c7714, some c7626, some c7627, some c7355, some c7676, some c7670, some c1450, some c1449, some c1444, some c7590, some c7742, some c7749, some c1356, some c2438, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7750 : lratChecker f7750 p7750 = .success := by decide +kernel
theorem unsat7750 : Unsatisfiable (PosFin 65) f7750 := by
  apply lratCheckerSound f7750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7750
  · intro a ha; simp [p7750] at ha; subst a; trivial
  · exact checked7750
theorem derived7750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7750 := by
  apply localUnsat_implies_entails f7750 [c7741, c7714, c7626, c7627, c7355, c7676, c7670, c1450, c1449, c1444, c7590, c7742, c7749, c1356, c2438] c7750 unsat7750 (by rfl) a
  have h0 : Entails.eval a c7741 := derived7741 a h
  have h1 : Entails.eval a c7714 := derived7714 a h
  have h2 : Entails.eval a c7626 := derived7626 a h
  have h3 : Entails.eval a c7627 := derived7627 a h
  have h4 : Entails.eval a c7355 := derived7355 a h
  have h5 : Entails.eval a c7676 := derived7676 a h
  have h6 : Entails.eval a c7670 := derived7670 a h
  have h7 : Entails.eval a c1450 := h 1449 (by decide)
  have h8 : Entails.eval a c1449 := h 1448 (by decide)
  have h9 : Entails.eval a c1444 := h 1443 (by decide)
  have h10 : Entails.eval a c7590 := derived7590 a h
  have h11 : Entails.eval a c7742 := derived7742 a h
  have h12 : Entails.eval a c7749 := derived7749 a h
  have h13 : Entails.eval a c1356 := h 1355 (by decide)
  have h14 : Entails.eval a c2438 := h 2437 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7751 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7751 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1462, some c1565, some c2070, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7751 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7751 : lratChecker f7751 p7751 = .success := by decide +kernel
theorem unsat7751 : Unsatisfiable (PosFin 65) f7751 := by
  apply lratCheckerSound f7751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7751
  · intro a ha; simp [p7751] at ha; subst a; trivial
  · exact checked7751
theorem derived7751 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7751 := by
  apply localUnsat_implies_entails f7751 [c1462, c1565, c2070] c7751 unsat7751 (by rfl) a
  have h0 : Entails.eval a c1462 := h 1461 (by decide)
  have h1 : Entails.eval a c1565 := h 1564 (by decide)
  have h2 : Entails.eval a c2070 := h 2069 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7752 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7752 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7629, some c7501, some c780, some c770, some c7528, some c7738, some c764, some c759, some c7632, some c750, some c7633, some c7634, some c775, some c7522, some c2334, some c768, some c7718, some c7717, some c7751, some c1901, some c1378, some c2155, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7752 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7752 : lratChecker f7752 p7752 = .success := by decide +kernel
theorem unsat7752 : Unsatisfiable (PosFin 65) f7752 := by
  apply lratCheckerSound f7752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7752
  · intro a ha; simp [p7752] at ha; subst a; trivial
  · exact checked7752
theorem derived7752 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7752 := by
  apply localUnsat_implies_entails f7752 [c7629, c7501, c780, c770, c7528, c7738, c764, c759, c7632, c750, c7633, c7634, c775, c7522, c2334, c768, c7718, c7717, c7751, c1901, c1378, c2155] c7752 unsat7752 (by rfl) a
  have h0 : Entails.eval a c7629 := derived7629 a h
  have h1 : Entails.eval a c7501 := derived7501 a h
  have h2 : Entails.eval a c780 := h 779 (by decide)
  have h3 : Entails.eval a c770 := h 769 (by decide)
  have h4 : Entails.eval a c7528 := derived7528 a h
  have h5 : Entails.eval a c7738 := derived7738 a h
  have h6 : Entails.eval a c764 := h 763 (by decide)
  have h7 : Entails.eval a c759 := h 758 (by decide)
  have h8 : Entails.eval a c7632 := derived7632 a h
  have h9 : Entails.eval a c750 := h 749 (by decide)
  have h10 : Entails.eval a c7633 := derived7633 a h
  have h11 : Entails.eval a c7634 := derived7634 a h
  have h12 : Entails.eval a c775 := h 774 (by decide)
  have h13 : Entails.eval a c7522 := derived7522 a h
  have h14 : Entails.eval a c2334 := h 2333 (by decide)
  have h15 : Entails.eval a c768 := h 767 (by decide)
  have h16 : Entails.eval a c7718 := derived7718 a h
  have h17 : Entails.eval a c7717 := derived7717 a h
  have h18 : Entails.eval a c7751 := derived7751 a h
  have h19 : Entails.eval a c1901 := h 1900 (by decide)
  have h20 : Entails.eval a c1378 := h 1377 (by decide)
  have h21 : Entails.eval a c2155 := h 2154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7753 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7753 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c903, some c869, some c1345, some c1895, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7753 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7753 : lratChecker f7753 p7753 = .success := by decide +kernel
theorem unsat7753 : Unsatisfiable (PosFin 65) f7753 := by
  apply lratCheckerSound f7753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7753
  · intro a ha; simp [p7753] at ha; subst a; trivial
  · exact checked7753
theorem derived7753 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7753 := by
  apply localUnsat_implies_entails f7753 [c903, c869, c1345, c1895] c7753 unsat7753 (by rfl) a
  have h0 : Entails.eval a c903 := h 902 (by decide)
  have h1 : Entails.eval a c869 := h 868 (by decide)
  have h2 : Entails.eval a c1345 := h 1344 (by decide)
  have h3 : Entails.eval a c1895 := h 1894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7754 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7754 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1449, some c1437, some c1442, some c1421, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7754 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7754 : lratChecker f7754 p7754 = .success := by decide +kernel
theorem unsat7754 : Unsatisfiable (PosFin 65) f7754 := by
  apply lratCheckerSound f7754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7754
  · intro a ha; simp [p7754] at ha; subst a; trivial
  · exact checked7754
theorem derived7754 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7754 := by
  apply localUnsat_implies_entails f7754 [c1449, c1437, c1442, c1421] c7754 unsat7754 (by rfl) a
  have h0 : Entails.eval a c1449 := h 1448 (by decide)
  have h1 : Entails.eval a c1437 := h 1436 (by decide)
  have h2 : Entails.eval a c1442 := h 1441 (by decide)
  have h3 : Entails.eval a c1421 := h 1420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7755 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7755 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7754, some c703, some c712, some c704, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7755 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7755 : lratChecker f7755 p7755 = .success := by decide +kernel
theorem unsat7755 : Unsatisfiable (PosFin 65) f7755 := by
  apply lratCheckerSound f7755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7755
  · intro a ha; simp [p7755] at ha; subst a; trivial
  · exact checked7755
theorem derived7755 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7755 := by
  apply localUnsat_implies_entails f7755 [c7754, c703, c712, c704] c7755 unsat7755 (by rfl) a
  have h0 : Entails.eval a c7754 := derived7754 a h
  have h1 : Entails.eval a c703 := h 702 (by decide)
  have h2 : Entails.eval a c712 := h 711 (by decide)
  have h3 : Entails.eval a c704 := h 703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7756 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7756 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7755, some c723, some c1435, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7756 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7756 : lratChecker f7756 p7756 = .success := by decide +kernel
theorem unsat7756 : Unsatisfiable (PosFin 65) f7756 := by
  apply lratCheckerSound f7756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7756
  · intro a ha; simp [p7756] at ha; subst a; trivial
  · exact checked7756
theorem derived7756 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7756 := by
  apply localUnsat_implies_entails f7756 [c7755, c723, c1435] c7756 unsat7756 (by rfl) a
  have h0 : Entails.eval a c7755 := derived7755 a h
  have h1 : Entails.eval a c723 := h 722 (by decide)
  have h2 : Entails.eval a c1435 := h 1434 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7757 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7757 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1445, some c1426, some c1444, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7757 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7757 : lratChecker f7757 p7757 = .success := by decide +kernel
theorem unsat7757 : Unsatisfiable (PosFin 65) f7757 := by
  apply lratCheckerSound f7757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7757
  · intro a ha; simp [p7757] at ha; subst a; trivial
  · exact checked7757
theorem derived7757 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7757 := by
  apply localUnsat_implies_entails f7757 [c1445, c1426, c1444] c7757 unsat7757 (by rfl) a
  have h0 : Entails.eval a c1445 := h 1444 (by decide)
  have h1 : Entails.eval a c1426 := h 1425 (by decide)
  have h2 : Entails.eval a c1444 := h 1443 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7758 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7758 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7756, some c7757, some c703, some c720, some c721, some c708, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p7758 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7758 : lratChecker f7758 p7758 = .success := by decide +kernel
theorem unsat7758 : Unsatisfiable (PosFin 65) f7758 := by
  apply lratCheckerSound f7758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7758
  · intro a ha; simp [p7758] at ha; subst a; trivial
  · exact checked7758
theorem derived7758 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7758 := by
  apply localUnsat_implies_entails f7758 [c7756, c7757, c703, c720, c721, c708] c7758 unsat7758 (by rfl) a
  have h0 : Entails.eval a c7756 := derived7756 a h
  have h1 : Entails.eval a c7757 := derived7757 a h
  have h2 : Entails.eval a c703 := h 702 (by decide)
  have h3 : Entails.eval a c720 := h 719 (by decide)
  have h4 : Entails.eval a c721 := h 720 (by decide)
  have h5 : Entails.eval a c708 := h 707 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7759 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7759 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7754, some c706, some c708, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7759 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7759 : lratChecker f7759 p7759 = .success := by decide +kernel
theorem unsat7759 : Unsatisfiable (PosFin 65) f7759 := by
  apply lratCheckerSound f7759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7759
  · intro a ha; simp [p7759] at ha; subst a; trivial
  · exact checked7759
theorem derived7759 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7759 := by
  apply localUnsat_implies_entails f7759 [c7754, c706, c708] c7759 unsat7759 (by rfl) a
  have h0 : Entails.eval a c7754 := derived7754 a h
  have h1 : Entails.eval a c706 := h 705 (by decide)
  have h2 : Entails.eval a c708 := h 707 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7760 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7760 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7759, some c723, some c1450, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7760 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7760 : lratChecker f7760 p7760 = .success := by decide +kernel
theorem unsat7760 : Unsatisfiable (PosFin 65) f7760 := by
  apply lratCheckerSound f7760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7760
  · intro a ha; simp [p7760] at ha; subst a; trivial
  · exact checked7760
theorem derived7760 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7760 := by
  apply localUnsat_implies_entails f7760 [c7759, c723, c1450] c7760 unsat7760 (by rfl) a
  have h0 : Entails.eval a c7759 := derived7759 a h
  have h1 : Entails.eval a c723 := h 722 (by decide)
  have h2 : Entails.eval a c1450 := h 1449 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7761 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7761 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7752, some c7758, some c7616, some c7753, some c7697, some c7760, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7761 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7761 : lratChecker f7761 p7761 = .success := by decide +kernel
theorem unsat7761 : Unsatisfiable (PosFin 65) f7761 := by
  apply lratCheckerSound f7761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7761
  · intro a ha; simp [p7761] at ha; subst a; trivial
  · exact checked7761
theorem derived7761 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7761 := by
  apply localUnsat_implies_entails f7761 [c7752, c7758, c7616, c7753, c7697, c7760] c7761 unsat7761 (by rfl) a
  have h0 : Entails.eval a c7752 := derived7752 a h
  have h1 : Entails.eval a c7758 := derived7758 a h
  have h2 : Entails.eval a c7616 := derived7616 a h
  have h3 : Entails.eval a c7753 := derived7753 a h
  have h4 : Entails.eval a c7697 := derived7697 a h
  have h5 : Entails.eval a c7760 := derived7760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7762 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7762 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1974, some c1369, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7762 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7762 : lratChecker f7762 p7762 = .success := by decide +kernel
theorem unsat7762 : Unsatisfiable (PosFin 65) f7762 := by
  apply lratCheckerSound f7762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7762
  · intro a ha; simp [p7762] at ha; subst a; trivial
  · exact checked7762
theorem derived7762 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7762 := by
  apply localUnsat_implies_entails f7762 [c1974, c1369] c7762 unsat7762 (by rfl) a
  have h0 : Entails.eval a c1974 := h 1973 (by decide)
  have h1 : Entails.eval a c1369 := h 1368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7763 : DefaultClause 65 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7763 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7752, some c7616, some c7758, some c7761, some c7757, some c710, some c700, some c7633, some c717, some c7697, some c7618, some c7762, some c1371, some c1901, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7763 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7763 : lratChecker f7763 p7763 = .success := by decide +kernel
theorem unsat7763 : Unsatisfiable (PosFin 65) f7763 := by
  apply lratCheckerSound f7763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7763
  · intro a ha; simp [p7763] at ha; subst a; trivial
  · exact checked7763
theorem derived7763 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7763 := by
  apply localUnsat_implies_entails f7763 [c7752, c7616, c7758, c7761, c7757, c710, c700, c7633, c717, c7697, c7618, c7762, c1371, c1901] c7763 unsat7763 (by rfl) a
  have h0 : Entails.eval a c7752 := derived7752 a h
  have h1 : Entails.eval a c7616 := derived7616 a h
  have h2 : Entails.eval a c7758 := derived7758 a h
  have h3 : Entails.eval a c7761 := derived7761 a h
  have h4 : Entails.eval a c7757 := derived7757 a h
  have h5 : Entails.eval a c710 := h 709 (by decide)
  have h6 : Entails.eval a c700 := h 699 (by decide)
  have h7 : Entails.eval a c7633 := derived7633 a h
  have h8 : Entails.eval a c717 := h 716 (by decide)
  have h9 : Entails.eval a c7697 := derived7697 a h
  have h10 : Entails.eval a c7618 := derived7618 a h
  have h11 : Entails.eval a c7762 := derived7762 a h
  have h12 : Entails.eval a c1371 := h 1370 (by decide)
  have h13 : Entails.eval a c1901 := h 1900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7764 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7764 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c7626, some c7470, some c7741, some c7750, some c7763, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7764 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7764 : lratChecker f7764 p7764 = .success := by decide +kernel
theorem unsat7764 : Unsatisfiable (PosFin 65) f7764 := by
  apply lratCheckerSound f7764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7764
  · intro a ha; simp [p7764] at ha; subst a; trivial
  · exact checked7764
theorem derived7764 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7764 := by
  apply localUnsat_implies_entails f7764 [c7714, c7626, c7470, c7741, c7750, c7763] c7764 unsat7764 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7470 := derived7470 a h
  have h3 : Entails.eval a c7741 := derived7741 a h
  have h4 : Entails.eval a c7750 := derived7750 a h
  have h5 : Entails.eval a c7763 := derived7763 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7765 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨27, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7765 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2991, some c2988, some c2984, some c2982, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7765 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7765 : lratChecker f7765 p7765 = .success := by decide +kernel
theorem unsat7765 : Unsatisfiable (PosFin 65) f7765 := by
  apply lratCheckerSound f7765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7765
  · intro a ha; simp [p7765] at ha; subst a; trivial
  · exact checked7765
theorem derived7765 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7765 := by
  apply localUnsat_implies_entails f7765 [c2991, c2988, c2984, c2982] c7765 unsat7765 (by rfl) a
  have h0 : Entails.eval a c2991 := h 2990 (by decide)
  have h1 : Entails.eval a c2988 := h 2987 (by decide)
  have h2 : Entails.eval a c2984 := h 2983 (by decide)
  have h3 : Entails.eval a c2982 := h 2981 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7766 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7766 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c970, some c1058, some c134, some c7765, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7766 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7766 : lratChecker f7766 p7766 = .success := by decide +kernel
theorem unsat7766 : Unsatisfiable (PosFin 65) f7766 := by
  apply lratCheckerSound f7766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7766
  · intro a ha; simp [p7766] at ha; subst a; trivial
  · exact checked7766
theorem derived7766 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7766 := by
  apply localUnsat_implies_entails f7766 [c970, c1058, c134, c7765] c7766 unsat7766 (by rfl) a
  have h0 : Entails.eval a c970 := h 969 (by decide)
  have h1 : Entails.eval a c1058 := h 1057 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c7765 := derived7765 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7767 : DefaultClause 65 := directClause [(⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7767 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c292, some c7221, some c7255, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7767 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7767 : lratChecker f7767 p7767 = .success := by decide +kernel
theorem unsat7767 : Unsatisfiable (PosFin 65) f7767 := by
  apply lratCheckerSound f7767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7767
  · intro a ha; simp [p7767] at ha; subst a; trivial
  · exact checked7767
theorem derived7767 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7767 := by
  apply localUnsat_implies_entails f7767 [c7714, c292, c7221, c7255] c7767 unsat7767 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c7221 := derived7221 a h
  have h3 : Entails.eval a c7255 := derived7255 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7768 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7768 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c732, some c733, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7768 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7768 : lratChecker f7768 p7768 = .success := by decide +kernel
theorem unsat7768 : Unsatisfiable (PosFin 65) f7768 := by
  apply lratCheckerSound f7768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7768
  · intro a ha; simp [p7768] at ha; subst a; trivial
  · exact checked7768
theorem derived7768 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7768 := by
  apply localUnsat_implies_entails f7768 [c732, c733] c7768 unsat7768 (by rfl) a
  have h0 : Entails.eval a c732 := h 731 (by decide)
  have h1 : Entails.eval a c733 := h 732 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7769 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7769 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c973, some c2113, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7769 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7769 : lratChecker f7769 p7769 = .success := by decide +kernel
theorem unsat7769 : Unsatisfiable (PosFin 65) f7769 := by
  apply lratCheckerSound f7769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7769
  · intro a ha; simp [p7769] at ha; subst a; trivial
  · exact checked7769
theorem derived7769 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7769 := by
  apply localUnsat_implies_entails f7769 [c973, c2113] c7769 unsat7769 (by rfl) a
  have h0 : Entails.eval a c973 := h 972 (by decide)
  have h1 : Entails.eval a c2113 := h 2112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7770 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7770 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7646, some c7688, some c7657, some c398, some c418, some c412, some c7768, some c7590, some c1541, some c1551, some c7769, some c974, some c2117, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7770 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7770 : lratChecker f7770 p7770 = .success := by decide +kernel
theorem unsat7770 : Unsatisfiable (PosFin 65) f7770 := by
  apply lratCheckerSound f7770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7770
  · intro a ha; simp [p7770] at ha; subst a; trivial
  · exact checked7770
theorem derived7770 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7770 := by
  apply localUnsat_implies_entails f7770 [c7646, c7688, c7657, c398, c418, c412, c7768, c7590, c1541, c1551, c7769, c974, c2117] c7770 unsat7770 (by rfl) a
  have h0 : Entails.eval a c7646 := derived7646 a h
  have h1 : Entails.eval a c7688 := derived7688 a h
  have h2 : Entails.eval a c7657 := derived7657 a h
  have h3 : Entails.eval a c398 := h 397 (by decide)
  have h4 : Entails.eval a c418 := h 417 (by decide)
  have h5 : Entails.eval a c412 := h 411 (by decide)
  have h6 : Entails.eval a c7768 := derived7768 a h
  have h7 : Entails.eval a c7590 := derived7590 a h
  have h8 : Entails.eval a c1541 := h 1540 (by decide)
  have h9 : Entails.eval a c1551 := h 1550 (by decide)
  have h10 : Entails.eval a c7769 := derived7769 a h
  have h11 : Entails.eval a c974 := h 973 (by decide)
  have h12 : Entails.eval a c2117 := h 2116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7771 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7771 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7770, some c1122, some c392, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7771 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7771 : lratChecker f7771 p7771 = .success := by decide +kernel
theorem unsat7771 : Unsatisfiable (PosFin 65) f7771 := by
  apply lratCheckerSound f7771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7771
  · intro a ha; simp [p7771] at ha; subst a; trivial
  · exact checked7771
theorem derived7771 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7771 := by
  apply localUnsat_implies_entails f7771 [c7770, c1122, c392] c7771 unsat7771 (by rfl) a
  have h0 : Entails.eval a c7770 := derived7770 a h
  have h1 : Entails.eval a c1122 := h 1121 (by decide)
  have h2 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7772 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7772 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7764, some c7626, some c7470, some c7688, some c7767, some c7766, some c7771, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7772 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7772 : lratChecker f7772 p7772 = .success := by decide +kernel
theorem unsat7772 : Unsatisfiable (PosFin 65) f7772 := by
  apply lratCheckerSound f7772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7772
  · intro a ha; simp [p7772] at ha; subst a; trivial
  · exact checked7772
theorem derived7772 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7772 := by
  apply localUnsat_implies_entails f7772 [c7764, c7626, c7470, c7688, c7767, c7766, c7771] c7772 unsat7772 (by rfl) a
  have h0 : Entails.eval a c7764 := derived7764 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7470 := derived7470 a h
  have h3 : Entails.eval a c7688 := derived7688 a h
  have h4 : Entails.eval a c7767 := derived7767 a h
  have h5 : Entails.eval a c7766 := derived7766 a h
  have h6 : Entails.eval a c7771 := derived7771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7773 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7773 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1114, some c1128, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7773 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7773 : lratChecker f7773 p7773 = .success := by decide +kernel
theorem unsat7773 : Unsatisfiable (PosFin 65) f7773 := by
  apply lratCheckerSound f7773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7773
  · intro a ha; simp [p7773] at ha; subst a; trivial
  · exact checked7773
theorem derived7773 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7773 := by
  apply localUnsat_implies_entails f7773 [c1114, c1128] c7773 unsat7773 (by rfl) a
  have h0 : Entails.eval a c1114 := h 1113 (by decide)
  have h1 : Entails.eval a c1128 := h 1127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7774 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7774 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7773, some c7331, some c398, some c1385, some c1056, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7774 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7774 : lratChecker f7774 p7774 = .success := by decide +kernel
theorem unsat7774 : Unsatisfiable (PosFin 65) f7774 := by
  apply lratCheckerSound f7774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7774
  · intro a ha; simp [p7774] at ha; subst a; trivial
  · exact checked7774
theorem derived7774 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7774 := by
  apply localUnsat_implies_entails f7774 [c7773, c7331, c398, c1385, c1056] c7774 unsat7774 (by rfl) a
  have h0 : Entails.eval a c7773 := derived7773 a h
  have h1 : Entails.eval a c7331 := derived7331 a h
  have h2 : Entails.eval a c398 := h 397 (by decide)
  have h3 : Entails.eval a c1385 := h 1384 (by decide)
  have h4 : Entails.eval a c1056 := h 1055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7775 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7775 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7772, some c7764, some c7714, some c7626, some c7470, some c7774, some c7766, some c7657, some c398, some c413, some c400, some c406, some c381, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7775 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7775 : lratChecker f7775 p7775 = .success := by decide +kernel
theorem unsat7775 : Unsatisfiable (PosFin 65) f7775 := by
  apply lratCheckerSound f7775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7775
  · intro a ha; simp [p7775] at ha; subst a; trivial
  · exact checked7775
theorem derived7775 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7775 := by
  apply localUnsat_implies_entails f7775 [c7772, c7764, c7714, c7626, c7470, c7774, c7766, c7657, c398, c413, c400, c406, c381] c7775 unsat7775 (by rfl) a
  have h0 : Entails.eval a c7772 := derived7772 a h
  have h1 : Entails.eval a c7764 := derived7764 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7626 := derived7626 a h
  have h4 : Entails.eval a c7470 := derived7470 a h
  have h5 : Entails.eval a c7774 := derived7774 a h
  have h6 : Entails.eval a c7766 := derived7766 a h
  have h7 : Entails.eval a c7657 := derived7657 a h
  have h8 : Entails.eval a c398 := h 397 (by decide)
  have h9 : Entails.eval a c413 := h 412 (by decide)
  have h10 : Entails.eval a c400 := h 399 (by decide)
  have h11 : Entails.eval a c406 := h 405 (by decide)
  have h12 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7776 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7776 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7331, some c1384, some c1056, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7776 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7776 : lratChecker f7776 p7776 = .success := by decide +kernel
theorem unsat7776 : Unsatisfiable (PosFin 65) f7776 := by
  apply lratCheckerSound f7776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7776
  · intro a ha; simp [p7776] at ha; subst a; trivial
  · exact checked7776
theorem derived7776 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7776 := by
  apply localUnsat_implies_entails f7776 [c7331, c1384, c1056] c7776 unsat7776 (by rfl) a
  have h0 : Entails.eval a c7331 := derived7331 a h
  have h1 : Entails.eval a c1384 := h 1383 (by decide)
  have h2 : Entails.eval a c1056 := h 1055 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7777 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7777 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7776, some c1114, some c1112, some c1138, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7777 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7777 : lratChecker f7777 p7777 = .success := by decide +kernel
theorem unsat7777 : Unsatisfiable (PosFin 65) f7777 := by
  apply lratCheckerSound f7777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7777
  · intro a ha; simp [p7777] at ha; subst a; trivial
  · exact checked7777
theorem derived7777 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7777 := by
  apply localUnsat_implies_entails f7777 [c7776, c1114, c1112, c1138] c7777 unsat7777 (by rfl) a
  have h0 : Entails.eval a c7776 := derived7776 a h
  have h1 : Entails.eval a c1114 := h 1113 (by decide)
  have h2 : Entails.eval a c1112 := h 1111 (by decide)
  have h3 : Entails.eval a c1138 := h 1137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7778 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7778 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7764, some c7772, some c7777, some c7775, some c7766, some c7694, some c1125, some c1126, some c1134, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7778 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked7778 : lratChecker f7778 p7778 = .success := by decide +kernel
theorem unsat7778 : Unsatisfiable (PosFin 65) f7778 := by
  apply lratCheckerSound f7778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7778
  · intro a ha; simp [p7778] at ha; subst a; trivial
  · exact checked7778
theorem derived7778 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7778 := by
  apply localUnsat_implies_entails f7778 [c7470, c7626, c7714, c7764, c7772, c7777, c7775, c7766, c7694, c1125, c1126, c1134] c7778 unsat7778 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7764 := derived7764 a h
  have h4 : Entails.eval a c7772 := derived7772 a h
  have h5 : Entails.eval a c7777 := derived7777 a h
  have h6 : Entails.eval a c7775 := derived7775 a h
  have h7 : Entails.eval a c7766 := derived7766 a h
  have h8 : Entails.eval a c7694 := derived7694 a h
  have h9 : Entails.eval a c1125 := h 1124 (by decide)
  have h10 : Entails.eval a c1126 := h 1125 (by decide)
  have h11 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7779 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7779 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7777, some c7656, some c7331, some c398, some c314, some c982, some c418, some c1704, some c1778, some c2064, some c1970, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7779 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7779 : lratChecker f7779 p7779 = .success := by decide +kernel
theorem unsat7779 : Unsatisfiable (PosFin 65) f7779 := by
  apply lratCheckerSound f7779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7779
  · intro a ha; simp [p7779] at ha; subst a; trivial
  · exact checked7779
theorem derived7779 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7779 := by
  apply localUnsat_implies_entails f7779 [c7777, c7656, c7331, c398, c314, c982, c418, c1704, c1778, c2064, c1970] c7779 unsat7779 (by rfl) a
  have h0 : Entails.eval a c7777 := derived7777 a h
  have h1 : Entails.eval a c7656 := derived7656 a h
  have h2 : Entails.eval a c7331 := derived7331 a h
  have h3 : Entails.eval a c398 := h 397 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c982 := h 981 (by decide)
  have h6 : Entails.eval a c418 := h 417 (by decide)
  have h7 : Entails.eval a c1704 := h 1703 (by decide)
  have h8 : Entails.eval a c1778 := h 1777 (by decide)
  have h9 : Entails.eval a c2064 := h 2063 (by decide)
  have h10 : Entails.eval a c1970 := h 1969 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7780 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7780 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7777, some c7779, some c1108, some c1128, some c1120, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7780 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7780 : lratChecker f7780 p7780 = .success := by decide +kernel
theorem unsat7780 : Unsatisfiable (PosFin 65) f7780 := by
  apply lratCheckerSound f7780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7780
  · intro a ha; simp [p7780] at ha; subst a; trivial
  · exact checked7780
theorem derived7780 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7780 := by
  apply localUnsat_implies_entails f7780 [c7777, c7779, c1108, c1128, c1120] c7780 unsat7780 (by rfl) a
  have h0 : Entails.eval a c7777 := derived7777 a h
  have h1 : Entails.eval a c7779 := derived7779 a h
  have h2 : Entails.eval a c1108 := h 1107 (by decide)
  have h3 : Entails.eval a c1128 := h 1127 (by decide)
  have h4 : Entails.eval a c1120 := h 1119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived7780

end CochromaticTwenty.Certificates.FixedCore1
