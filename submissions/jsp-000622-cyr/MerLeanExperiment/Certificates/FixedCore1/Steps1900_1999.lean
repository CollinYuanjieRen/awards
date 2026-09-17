import MerLeanExperiment.Certificates.FixedCore1.Steps1800_1899

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7781 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7781 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7656, some c7331, some c314, some c982, some c394, some c393, some c1778, some c2067, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7781 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7781 : lratChecker f7781 p7781 = .success := by decide +kernel
theorem unsat7781 : Unsatisfiable (PosFin 65) f7781 := by
  apply lratCheckerSound f7781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7781
  · intro a ha; simp [p7781] at ha; subst a; trivial
  · exact checked7781
theorem derived7781 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7781 := by
  apply localUnsat_implies_entails f7781 [c7656, c7331, c314, c982, c394, c393, c1778, c2067] c7781 unsat7781 (by rfl) a
  have h0 : Entails.eval a c7656 := derived7656 a h
  have h1 : Entails.eval a c7331 := derived7331 a h
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c982 := h 981 (by decide)
  have h4 : Entails.eval a c394 := h 393 (by decide)
  have h5 : Entails.eval a c393 := h 392 (by decide)
  have h6 : Entails.eval a c1778 := h 1777 (by decide)
  have h7 : Entails.eval a c2067 := h 2066 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7782 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7782 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1124, some c1123, some c1134, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7782 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7782 : lratChecker f7782 p7782 = .success := by decide +kernel
theorem unsat7782 : Unsatisfiable (PosFin 65) f7782 := by
  apply lratCheckerSound f7782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7782
  · intro a ha; simp [p7782] at ha; subst a; trivial
  · exact checked7782
theorem derived7782 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7782 := by
  apply localUnsat_implies_entails f7782 [c1124, c1123, c1134] c7782 unsat7782 (by rfl) a
  have h0 : Entails.eval a c1124 := h 1123 (by decide)
  have h1 : Entails.eval a c1123 := h 1122 (by decide)
  have h2 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7783 : DefaultClause 65 := directClause [(⟨59, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7783 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c61, some c62, some c6682, some (DefaultClause.unit (⟨59, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p7783 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7783 : lratChecker f7783 p7783 = .success := by decide +kernel
theorem unsat7783 : Unsatisfiable (PosFin 65) f7783 := by
  apply lratCheckerSound f7783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7783
  · intro a ha; simp [p7783] at ha; subst a; trivial
  · exact checked7783
theorem derived7783 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7783 := by
  apply localUnsat_implies_entails f7783 [c61, c62, c6682] c7783 unsat7783 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c6682 := derived6682 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7784 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7784 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7764, some c7772, some c7778, some c7780, some c7781, some c7777, some c7782, some c1129, some c7716, some c1121, some c1138, some c1120, some c7738, some c7522, some c7718, some c2526, some c7717, some c7719, some c7783, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7784 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked7784 : lratChecker f7784 p7784 = .success := by decide +kernel
theorem unsat7784 : Unsatisfiable (PosFin 65) f7784 := by
  apply lratCheckerSound f7784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7784
  · intro a ha; simp [p7784] at ha; subst a; trivial
  · exact checked7784
theorem derived7784 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7784 := by
  apply localUnsat_implies_entails f7784 [c7470, c7626, c7714, c7764, c7772, c7778, c7780, c7781, c7777, c7782, c1129, c7716, c1121, c1138, c1120, c7738, c7522, c7718, c2526, c7717, c7719, c7783] c7784 unsat7784 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7764 := derived7764 a h
  have h4 : Entails.eval a c7772 := derived7772 a h
  have h5 : Entails.eval a c7778 := derived7778 a h
  have h6 : Entails.eval a c7780 := derived7780 a h
  have h7 : Entails.eval a c7781 := derived7781 a h
  have h8 : Entails.eval a c7777 := derived7777 a h
  have h9 : Entails.eval a c7782 := derived7782 a h
  have h10 : Entails.eval a c1129 := h 1128 (by decide)
  have h11 : Entails.eval a c7716 := derived7716 a h
  have h12 : Entails.eval a c1121 := h 1120 (by decide)
  have h13 : Entails.eval a c1138 := h 1137 (by decide)
  have h14 : Entails.eval a c1120 := h 1119 (by decide)
  have h15 : Entails.eval a c7738 := derived7738 a h
  have h16 : Entails.eval a c7522 := derived7522 a h
  have h17 : Entails.eval a c7718 := derived7718 a h
  have h18 : Entails.eval a c2526 := h 2525 (by decide)
  have h19 : Entails.eval a c7717 := derived7717 a h
  have h20 : Entails.eval a c7719 := derived7719 a h
  have h21 : Entails.eval a c7783 := derived7783 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7785 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7785 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c313, some c322, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7785 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7785 : lratChecker f7785 p7785 = .success := by decide +kernel
theorem unsat7785 : Unsatisfiable (PosFin 65) f7785 := by
  apply lratCheckerSound f7785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7785
  · intro a ha; simp [p7785] at ha; subst a; trivial
  · exact checked7785
theorem derived7785 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7785 := by
  apply localUnsat_implies_entails f7785 [c313, c322] c7785 unsat7785 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7786 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7786 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7778, some c7470, some c7626, some c7714, some c7764, some c7772, some c7777, some c7780, some c7781, some c7782, some c1138, some c1129, some c7738, some c1120, some c1121, some c7716, some c1134, some c7784, some c7737, some c7785, some c1789, some c7719, some c40, some c6683, some c39, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7786 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked7786 : lratChecker f7786 p7786 = .success := by decide +kernel
theorem unsat7786 : Unsatisfiable (PosFin 65) f7786 := by
  apply lratCheckerSound f7786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7786
  · intro a ha; simp [p7786] at ha; subst a; trivial
  · exact checked7786
theorem derived7786 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7786 := by
  apply localUnsat_implies_entails f7786 [c7778, c7470, c7626, c7714, c7764, c7772, c7777, c7780, c7781, c7782, c1138, c1129, c7738, c1120, c1121, c7716, c1134, c7784, c7737, c7785, c1789, c7719, c40, c6683, c39] c7786 unsat7786 (by rfl) a
  have h0 : Entails.eval a c7778 := derived7778 a h
  have h1 : Entails.eval a c7470 := derived7470 a h
  have h2 : Entails.eval a c7626 := derived7626 a h
  have h3 : Entails.eval a c7714 := derived7714 a h
  have h4 : Entails.eval a c7764 := derived7764 a h
  have h5 : Entails.eval a c7772 := derived7772 a h
  have h6 : Entails.eval a c7777 := derived7777 a h
  have h7 : Entails.eval a c7780 := derived7780 a h
  have h8 : Entails.eval a c7781 := derived7781 a h
  have h9 : Entails.eval a c7782 := derived7782 a h
  have h10 : Entails.eval a c1138 := h 1137 (by decide)
  have h11 : Entails.eval a c1129 := h 1128 (by decide)
  have h12 : Entails.eval a c7738 := derived7738 a h
  have h13 : Entails.eval a c1120 := h 1119 (by decide)
  have h14 : Entails.eval a c1121 := h 1120 (by decide)
  have h15 : Entails.eval a c7716 := derived7716 a h
  have h16 : Entails.eval a c1134 := h 1133 (by decide)
  have h17 : Entails.eval a c7784 := derived7784 a h
  have h18 : Entails.eval a c7737 := derived7737 a h
  have h19 : Entails.eval a c7785 := derived7785 a h
  have h20 : Entails.eval a c1789 := h 1788 (by decide)
  have h21 : Entails.eval a c7719 := derived7719 a h
  have h22 : Entails.eval a c40 := h 39 (by decide)
  have h23 : Entails.eval a c6683 := derived6683 a h
  have h24 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7787 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7787 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7657, some c7656, some c7331, some c314, some c982, some c1778, some c2064, some c2065, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7787 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7787 : lratChecker f7787 p7787 = .success := by decide +kernel
theorem unsat7787 : Unsatisfiable (PosFin 65) f7787 := by
  apply lratCheckerSound f7787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7787
  · intro a ha; simp [p7787] at ha; subst a; trivial
  · exact checked7787
theorem derived7787 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7787 := by
  apply localUnsat_implies_entails f7787 [c7657, c7656, c7331, c314, c982, c1778, c2064, c2065] c7787 unsat7787 (by rfl) a
  have h0 : Entails.eval a c7657 := derived7657 a h
  have h1 : Entails.eval a c7656 := derived7656 a h
  have h2 : Entails.eval a c7331 := derived7331 a h
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c982 := h 981 (by decide)
  have h5 : Entails.eval a c1778 := h 1777 (by decide)
  have h6 : Entails.eval a c2064 := h 2063 (by decide)
  have h7 : Entails.eval a c2065 := h 2064 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7788 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7788 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7787, some c7781, some c1126, some c1125, some c1134, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7788 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7788 : lratChecker f7788 p7788 = .success := by decide +kernel
theorem unsat7788 : Unsatisfiable (PosFin 65) f7788 := by
  apply lratCheckerSound f7788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7788
  · intro a ha; simp [p7788] at ha; subst a; trivial
  · exact checked7788
theorem derived7788 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7788 := by
  apply localUnsat_implies_entails f7788 [c7787, c7781, c1126, c1125, c1134] c7788 unsat7788 (by rfl) a
  have h0 : Entails.eval a c7787 := derived7787 a h
  have h1 : Entails.eval a c7781 := derived7781 a h
  have h2 : Entails.eval a c1126 := h 1125 (by decide)
  have h3 : Entails.eval a c1125 := h 1124 (by decide)
  have h4 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7789 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7789 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7764, some c7714, some c7626, some c7470, some c7772, some c7778, some c7786, some c7788, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7789 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7789 : lratChecker f7789 p7789 = .success := by decide +kernel
theorem unsat7789 : Unsatisfiable (PosFin 65) f7789 := by
  apply lratCheckerSound f7789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7789
  · intro a ha; simp [p7789] at ha; subst a; trivial
  · exact checked7789
theorem derived7789 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7789 := by
  apply localUnsat_implies_entails f7789 [c7764, c7714, c7626, c7470, c7772, c7778, c7786, c7788] c7789 unsat7789 (by rfl) a
  have h0 : Entails.eval a c7764 := derived7764 a h
  have h1 : Entails.eval a c7714 := derived7714 a h
  have h2 : Entails.eval a c7626 := derived7626 a h
  have h3 : Entails.eval a c7470 := derived7470 a h
  have h4 : Entails.eval a c7772 := derived7772 a h
  have h5 : Entails.eval a c7778 := derived7778 a h
  have h6 : Entails.eval a c7786 := derived7786 a h
  have h7 : Entails.eval a c7788 := derived7788 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7790 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7790 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7764, some c7688, some c7766, some c7646, some c7789, some c7657, some c7748, some c7768, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7790 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7790 : lratChecker f7790 p7790 = .success := by decide +kernel
theorem unsat7790 : Unsatisfiable (PosFin 65) f7790 := by
  apply lratCheckerSound f7790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7790
  · intro a ha; simp [p7790] at ha; subst a; trivial
  · exact checked7790
theorem derived7790 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7790 := by
  apply localUnsat_implies_entails f7790 [c7470, c7626, c7764, c7688, c7766, c7646, c7789, c7657, c7748, c7768] c7790 unsat7790 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7764 := derived7764 a h
  have h3 : Entails.eval a c7688 := derived7688 a h
  have h4 : Entails.eval a c7766 := derived7766 a h
  have h5 : Entails.eval a c7646 := derived7646 a h
  have h6 : Entails.eval a c7789 := derived7789 a h
  have h7 : Entails.eval a c7657 := derived7657 a h
  have h8 : Entails.eval a c7748 := derived7748 a h
  have h9 : Entails.eval a c7768 := derived7768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7791 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7791 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c978, some c1066, some c1122, some c2029, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p7791 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7791 : lratChecker f7791 p7791 = .success := by decide +kernel
theorem unsat7791 : Unsatisfiable (PosFin 65) f7791 := by
  apply lratCheckerSound f7791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7791
  · intro a ha; simp [p7791] at ha; subst a; trivial
  · exact checked7791
theorem derived7791 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7791 := by
  apply localUnsat_implies_entails f7791 [c978, c1066, c1122, c2029] c7791 unsat7791 (by rfl) a
  have h0 : Entails.eval a c978 := h 977 (by decide)
  have h1 : Entails.eval a c1066 := h 1065 (by decide)
  have h2 : Entails.eval a c1122 := h 1121 (by decide)
  have h3 : Entails.eval a c2029 := h 2028 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7792 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7792 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7764, some c7470, some c7688, some c7766, some c7790, some c7791, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7792 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7792 : lratChecker f7792 p7792 = .success := by decide +kernel
theorem unsat7792 : Unsatisfiable (PosFin 65) f7792 := by
  apply lratCheckerSound f7792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7792
  · intro a ha; simp [p7792] at ha; subst a; trivial
  · exact checked7792
theorem derived7792 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7792 := by
  apply localUnsat_implies_entails f7792 [c7764, c7470, c7688, c7766, c7790, c7791] c7792 unsat7792 (by rfl) a
  have h0 : Entails.eval a c7764 := derived7764 a h
  have h1 : Entails.eval a c7470 := derived7470 a h
  have h2 : Entails.eval a c7688 := derived7688 a h
  have h3 : Entails.eval a c7766 := derived7766 a h
  have h4 : Entails.eval a c7790 := derived7790 a h
  have h5 : Entails.eval a c7791 := derived7791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7793 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7793 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7764, some c7714, some c7470, some c7792, some c981, some c1073, some c135, some c3066, some c3347, some c3343, some c3342, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7793 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7793 : lratChecker f7793 p7793 = .success := by decide +kernel
theorem unsat7793 : Unsatisfiable (PosFin 65) f7793 := by
  apply lratCheckerSound f7793 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7793
  · intro a ha; simp [p7793] at ha; subst a; trivial
  · exact checked7793
theorem derived7793 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7793 := by
  apply localUnsat_implies_entails f7793 [c7764, c7714, c7470, c7792, c981, c1073, c135, c3066, c3347, c3343, c3342] c7793 unsat7793 (by rfl) a
  have h0 : Entails.eval a c7764 := derived7764 a h
  have h1 : Entails.eval a c7714 := derived7714 a h
  have h2 : Entails.eval a c7470 := derived7470 a h
  have h3 : Entails.eval a c7792 := derived7792 a h
  have h4 : Entails.eval a c981 := h 980 (by decide)
  have h5 : Entails.eval a c1073 := h 1072 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c3066 := h 3065 (by decide)
  have h8 : Entails.eval a c3347 := h 3346 (by decide)
  have h9 : Entails.eval a c3343 := h 3342 (by decide)
  have h10 : Entails.eval a c3342 := h 3341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7794 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7794 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7581, some c7573, some c7582, some c1060, some c1071, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7794 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7794 : lratChecker f7794 p7794 = .success := by decide +kernel
theorem unsat7794 : Unsatisfiable (PosFin 65) f7794 := by
  apply lratCheckerSound f7794 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7794
  · intro a ha; simp [p7794] at ha; subst a; trivial
  · exact checked7794
theorem derived7794 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7794 := by
  apply localUnsat_implies_entails f7794 [c7581, c7573, c7582, c1060, c1071] c7794 unsat7794 (by rfl) a
  have h0 : Entails.eval a c7581 := derived7581 a h
  have h1 : Entails.eval a c7573 := derived7573 a h
  have h2 : Entails.eval a c7582 := derived7582 a h
  have h3 : Entails.eval a c1060 := h 1059 (by decide)
  have h4 : Entails.eval a c1071 := h 1070 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7795 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7795 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7660, some c7794, some c1114, some c1112, some c1138, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7795 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7795 : lratChecker f7795 p7795 = .success := by decide +kernel
theorem unsat7795 : Unsatisfiable (PosFin 65) f7795 := by
  apply lratCheckerSound f7795 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7795
  · intro a ha; simp [p7795] at ha; subst a; trivial
  · exact checked7795
theorem derived7795 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7795 := by
  apply localUnsat_implies_entails f7795 [c7660, c7794, c1114, c1112, c1138] c7795 unsat7795 (by rfl) a
  have h0 : Entails.eval a c7660 := derived7660 a h
  have h1 : Entails.eval a c7794 := derived7794 a h
  have h2 : Entails.eval a c1114 := h 1113 (by decide)
  have h3 : Entails.eval a c1112 := h 1111 (by decide)
  have h4 : Entails.eval a c1138 := h 1137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7796 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7796 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c806, some c796, some c800, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7796 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7796 : lratChecker f7796 p7796 = .success := by decide +kernel
theorem unsat7796 : Unsatisfiable (PosFin 65) f7796 := by
  apply lratCheckerSound f7796 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7796
  · intro a ha; simp [p7796] at ha; subst a; trivial
  · exact checked7796
theorem derived7796 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7796 := by
  apply localUnsat_implies_entails f7796 [c806, c796, c800] c7796 unsat7796 (by rfl) a
  have h0 : Entails.eval a c806 := h 805 (by decide)
  have h1 : Entails.eval a c796 := h 795 (by decide)
  have h2 : Entails.eval a c800 := h 799 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7797 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7797 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7796, some c7754, some c732, some c735, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7797 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7797 : lratChecker f7797 p7797 = .success := by decide +kernel
theorem unsat7797 : Unsatisfiable (PosFin 65) f7797 := by
  apply lratCheckerSound f7797 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7797
  · intro a ha; simp [p7797] at ha; subst a; trivial
  · exact checked7797
theorem derived7797 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7797 := by
  apply localUnsat_implies_entails f7797 [c7796, c7754, c732, c735] c7797 unsat7797 (by rfl) a
  have h0 : Entails.eval a c7796 := derived7796 a h
  have h1 : Entails.eval a c7754 := derived7754 a h
  have h2 : Entails.eval a c732 := h 731 (by decide)
  have h3 : Entails.eval a c735 := h 734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7798 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7798 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7657, some c7796, some c7797, some c737, some c1435, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7798 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7798 : lratChecker f7798 p7798 = .success := by decide +kernel
theorem unsat7798 : Unsatisfiable (PosFin 65) f7798 := by
  apply lratCheckerSound f7798 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7798
  · intro a ha; simp [p7798] at ha; subst a; trivial
  · exact checked7798
theorem derived7798 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7798 := by
  apply localUnsat_implies_entails f7798 [c7657, c7796, c7797, c737, c1435] c7798 unsat7798 (by rfl) a
  have h0 : Entails.eval a c7657 := derived7657 a h
  have h1 : Entails.eval a c7796 := derived7796 a h
  have h2 : Entails.eval a c7797 := derived7797 a h
  have h3 : Entails.eval a c737 := h 736 (by decide)
  have h4 : Entails.eval a c1435 := h 1434 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7799 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7799 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7528, some c804, some c798, some c807, some c799, some c801, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7799 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7799 : lratChecker f7799 p7799 = .success := by decide +kernel
theorem unsat7799 : Unsatisfiable (PosFin 65) f7799 := by
  apply lratCheckerSound f7799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7799
  · intro a ha; simp [p7799] at ha; subst a; trivial
  · exact checked7799
theorem derived7799 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7799 := by
  apply localUnsat_implies_entails f7799 [c7528, c804, c798, c807, c799, c801] c7799 unsat7799 (by rfl) a
  have h0 : Entails.eval a c7528 := derived7528 a h
  have h1 : Entails.eval a c804 := h 803 (by decide)
  have h2 : Entails.eval a c798 := h 797 (by decide)
  have h3 : Entails.eval a c807 := h 806 (by decide)
  have h4 : Entails.eval a c799 := h 798 (by decide)
  have h5 : Entails.eval a c801 := h 800 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7800 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7800 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7795, some c7799, some c7697, some c7639, some c7698, some c2067, some c2123, some c2276, some c1059, some c1934, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7800 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7800 : lratChecker f7800 p7800 = .success := by decide +kernel
theorem unsat7800 : Unsatisfiable (PosFin 65) f7800 := by
  apply lratCheckerSound f7800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7800
  · intro a ha; simp [p7800] at ha; subst a; trivial
  · exact checked7800
theorem derived7800 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7800 := by
  apply localUnsat_implies_entails f7800 [c7795, c7799, c7697, c7639, c7698, c2067, c2123, c2276, c1059, c1934] c7800 unsat7800 (by rfl) a
  have h0 : Entails.eval a c7795 := derived7795 a h
  have h1 : Entails.eval a c7799 := derived7799 a h
  have h2 : Entails.eval a c7697 := derived7697 a h
  have h3 : Entails.eval a c7639 := derived7639 a h
  have h4 : Entails.eval a c7698 := derived7698 a h
  have h5 : Entails.eval a c2067 := h 2066 (by decide)
  have h6 : Entails.eval a c2123 := h 2122 (by decide)
  have h7 : Entails.eval a c2276 := h 2275 (by decide)
  have h8 : Entails.eval a c1059 := h 1058 (by decide)
  have h9 : Entails.eval a c1934 := h 1933 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7801 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7801 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7800, some c1125, some c1126, some c1134, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7801 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7801 : lratChecker f7801 p7801 = .success := by decide +kernel
theorem unsat7801 : Unsatisfiable (PosFin 65) f7801 := by
  apply lratCheckerSound f7801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7801
  · intro a ha; simp [p7801] at ha; subst a; trivial
  · exact checked7801
theorem derived7801 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7801 := by
  apply localUnsat_implies_entails f7801 [c7800, c1125, c1126, c1134] c7801 unsat7801 (by rfl) a
  have h0 : Entails.eval a c7800 := derived7800 a h
  have h1 : Entails.eval a c1125 := h 1124 (by decide)
  have h2 : Entails.eval a c1126 := h 1125 (by decide)
  have h3 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7802 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7802 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7798, some c7801, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7802 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7802 : lratChecker f7802 p7802 = .success := by decide +kernel
theorem unsat7802 : Unsatisfiable (PosFin 65) f7802 := by
  apply lratCheckerSound f7802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7802
  · intro a ha; simp [p7802] at ha; subst a; trivial
  · exact checked7802
theorem derived7802 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7802 := by
  apply localUnsat_implies_entails f7802 [c7798, c7801] c7802 unsat7802 (by rfl) a
  have h0 : Entails.eval a c7798 := derived7798 a h
  have h1 : Entails.eval a c7801 := derived7801 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7803 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7803 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7764, some c7789, some c7793, some c7795, some c7714, some c7766, some c7802, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7803 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7803 : lratChecker f7803 p7803 = .success := by decide +kernel
theorem unsat7803 : Unsatisfiable (PosFin 65) f7803 := by
  apply lratCheckerSound f7803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7803
  · intro a ha; simp [p7803] at ha; subst a; trivial
  · exact checked7803
theorem derived7803 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7803 := by
  apply localUnsat_implies_entails f7803 [c7470, c7626, c7764, c7789, c7793, c7795, c7714, c7766, c7802] c7803 unsat7803 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7764 := derived7764 a h
  have h3 : Entails.eval a c7789 := derived7789 a h
  have h4 : Entails.eval a c7793 := derived7793 a h
  have h5 : Entails.eval a c7795 := derived7795 a h
  have h6 : Entails.eval a c7714 := derived7714 a h
  have h7 : Entails.eval a c7766 := derived7766 a h
  have h8 : Entails.eval a c7802 := derived7802 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7804 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7804 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7796, some c7757, some c732, some c737, some c735, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7804 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7804 : lratChecker f7804 p7804 = .success := by decide +kernel
theorem unsat7804 : Unsatisfiable (PosFin 65) f7804 := by
  apply lratCheckerSound f7804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7804
  · intro a ha; simp [p7804] at ha; subst a; trivial
  · exact checked7804
theorem derived7804 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7804 := by
  apply localUnsat_implies_entails f7804 [c7796, c7757, c732, c737, c735] c7804 unsat7804 (by rfl) a
  have h0 : Entails.eval a c7796 := derived7796 a h
  have h1 : Entails.eval a c7757 := derived7757 a h
  have h2 : Entails.eval a c732 := h 731 (by decide)
  have h3 : Entails.eval a c737 := h 736 (by decide)
  have h4 : Entails.eval a c735 := h 734 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7805 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7805 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7804, some c1108, some c1128, some c1120, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7805 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7805 : lratChecker f7805 p7805 = .success := by decide +kernel
theorem unsat7805 : Unsatisfiable (PosFin 65) f7805 := by
  apply lratCheckerSound f7805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7805
  · intro a ha; simp [p7805] at ha; subst a; trivial
  · exact checked7805
theorem derived7805 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7805 := by
  apply localUnsat_implies_entails f7805 [c7804, c1108, c1128, c1120] c7805 unsat7805 (by rfl) a
  have h0 : Entails.eval a c7804 := derived7804 a h
  have h1 : Entails.eval a c1108 := h 1107 (by decide)
  have h2 : Entails.eval a c1128 := h 1127 (by decide)
  have h3 : Entails.eval a c1120 := h 1119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7806 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7806 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7532, some c7528, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7806 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7806 : lratChecker f7806 p7806 = .success := by decide +kernel
theorem unsat7806 : Unsatisfiable (PosFin 65) f7806 := by
  apply lratCheckerSound f7806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7806
  · intro a ha; simp [p7806] at ha; subst a; trivial
  · exact checked7806
theorem derived7806 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7806 := by
  apply localUnsat_implies_entails f7806 [c7532, c7528] c7806 unsat7806 (by rfl) a
  have h0 : Entails.eval a c7532 := derived7532 a h
  have h1 : Entails.eval a c7528 := derived7528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7807 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7807 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c745, some c735, some c868, some c2058, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7807 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7807 : lratChecker f7807 p7807 = .success := by decide +kernel
theorem unsat7807 : Unsatisfiable (PosFin 65) f7807 := by
  apply lratCheckerSound f7807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7807
  · intro a ha; simp [p7807] at ha; subst a; trivial
  · exact checked7807
theorem derived7807 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7807 := by
  apply localUnsat_implies_entails f7807 [c745, c735, c868, c2058] c7807 unsat7807 (by rfl) a
  have h0 : Entails.eval a c745 := h 744 (by decide)
  have h1 : Entails.eval a c735 := h 734 (by decide)
  have h2 : Entails.eval a c868 := h 867 (by decide)
  have h3 : Entails.eval a c2058 := h 2057 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7808 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7808 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c887, some c1075, some c1948, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7808 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7808 : lratChecker f7808 p7808 = .success := by decide +kernel
theorem unsat7808 : Unsatisfiable (PosFin 65) f7808 := by
  apply lratCheckerSound f7808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7808
  · intro a ha; simp [p7808] at ha; subst a; trivial
  · exact checked7808
theorem derived7808 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7808 := by
  apply localUnsat_implies_entails f7808 [c887, c1075, c1948] c7808 unsat7808 (by rfl) a
  have h0 : Entails.eval a c887 := h 886 (by decide)
  have h1 : Entails.eval a c1075 := h 1074 (by decide)
  have h2 : Entails.eval a c1948 := h 1947 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7809 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7809 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7795, some c7805, some c7618, some c7808, some c7633, some c7806, some c7757, some c7807, some c2068, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7809 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7809 : lratChecker f7809 p7809 = .success := by decide +kernel
theorem unsat7809 : Unsatisfiable (PosFin 65) f7809 := by
  apply lratCheckerSound f7809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7809
  · intro a ha; simp [p7809] at ha; subst a; trivial
  · exact checked7809
theorem derived7809 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7809 := by
  apply localUnsat_implies_entails f7809 [c7795, c7805, c7618, c7808, c7633, c7806, c7757, c7807, c2068] c7809 unsat7809 (by rfl) a
  have h0 : Entails.eval a c7795 := derived7795 a h
  have h1 : Entails.eval a c7805 := derived7805 a h
  have h2 : Entails.eval a c7618 := derived7618 a h
  have h3 : Entails.eval a c7808 := derived7808 a h
  have h4 : Entails.eval a c7633 := derived7633 a h
  have h5 : Entails.eval a c7806 := derived7806 a h
  have h6 : Entails.eval a c7757 := derived7757 a h
  have h7 : Entails.eval a c7807 := derived7807 a h
  have h8 : Entails.eval a c2068 := h 2067 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7810 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨19, by decide⟩, false), (⟨21, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨25, by decide⟩, false), (⟨20, by decide⟩, true), (⟨27, by decide⟩, true), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7810 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7633, some c7618, some c7522, some c7718, some c7751, some c7717, some c1560, some c2155, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7810 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7810 : lratChecker f7810 p7810 = .success := by decide +kernel
theorem unsat7810 : Unsatisfiable (PosFin 65) f7810 := by
  apply lratCheckerSound f7810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7810
  · intro a ha; simp [p7810] at ha; subst a; trivial
  · exact checked7810
theorem derived7810 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7810 := by
  apply localUnsat_implies_entails f7810 [c7633, c7618, c7522, c7718, c7751, c7717, c1560, c2155] c7810 unsat7810 (by rfl) a
  have h0 : Entails.eval a c7633 := derived7633 a h
  have h1 : Entails.eval a c7618 := derived7618 a h
  have h2 : Entails.eval a c7522 := derived7522 a h
  have h3 : Entails.eval a c7718 := derived7718 a h
  have h4 : Entails.eval a c7751 := derived7751 a h
  have h5 : Entails.eval a c7717 := derived7717 a h
  have h6 : Entails.eval a c1560 := h 1559 (by decide)
  have h7 : Entails.eval a c2155 := h 2154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7811 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7811 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1371, some c1901, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p7811 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7811 : lratChecker f7811 p7811 = .success := by decide +kernel
theorem unsat7811 : Unsatisfiable (PosFin 65) f7811 := by
  apply lratCheckerSound f7811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7811
  · intro a ha; simp [p7811] at ha; subst a; trivial
  · exact checked7811
theorem derived7811 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7811 := by
  apply localUnsat_implies_entails f7811 [c1371, c1901] c7811 unsat7811 (by rfl) a
  have h0 : Entails.eval a c1371 := h 1370 (by decide)
  have h1 : Entails.eval a c1901 := h 1900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7812 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7812 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7795, some c7805, some c7618, some c7808, some c7633, some c7809, some c1138, some c1129, some c7738, some c1120, some c1121, some c1134, some c7810, some c7811, some c2371, some c7751, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7812 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7812 : lratChecker f7812 p7812 = .success := by decide +kernel
theorem unsat7812 : Unsatisfiable (PosFin 65) f7812 := by
  apply lratCheckerSound f7812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7812
  · intro a ha; simp [p7812] at ha; subst a; trivial
  · exact checked7812
theorem derived7812 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7812 := by
  apply localUnsat_implies_entails f7812 [c7795, c7805, c7618, c7808, c7633, c7809, c1138, c1129, c7738, c1120, c1121, c1134, c7810, c7811, c2371, c7751] c7812 unsat7812 (by rfl) a
  have h0 : Entails.eval a c7795 := derived7795 a h
  have h1 : Entails.eval a c7805 := derived7805 a h
  have h2 : Entails.eval a c7618 := derived7618 a h
  have h3 : Entails.eval a c7808 := derived7808 a h
  have h4 : Entails.eval a c7633 := derived7633 a h
  have h5 : Entails.eval a c7809 := derived7809 a h
  have h6 : Entails.eval a c1138 := h 1137 (by decide)
  have h7 : Entails.eval a c1129 := h 1128 (by decide)
  have h8 : Entails.eval a c7738 := derived7738 a h
  have h9 : Entails.eval a c1120 := h 1119 (by decide)
  have h10 : Entails.eval a c1121 := h 1120 (by decide)
  have h11 : Entails.eval a c1134 := h 1133 (by decide)
  have h12 : Entails.eval a c7810 := derived7810 a h
  have h13 : Entails.eval a c7811 := derived7811 a h
  have h14 : Entails.eval a c2371 := h 2370 (by decide)
  have h15 : Entails.eval a c7751 := derived7751 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7813 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7813 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7812, some c7795, some c7805, some c7799, some c7757, some c7697, some c7639, some c2067, some c7698, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7813 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7813 : lratChecker f7813 p7813 = .success := by decide +kernel
theorem unsat7813 : Unsatisfiable (PosFin 65) f7813 := by
  apply lratCheckerSound f7813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7813
  · intro a ha; simp [p7813] at ha; subst a; trivial
  · exact checked7813
theorem derived7813 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7813 := by
  apply localUnsat_implies_entails f7813 [c7812, c7795, c7805, c7799, c7757, c7697, c7639, c2067, c7698] c7813 unsat7813 (by rfl) a
  have h0 : Entails.eval a c7812 := derived7812 a h
  have h1 : Entails.eval a c7795 := derived7795 a h
  have h2 : Entails.eval a c7805 := derived7805 a h
  have h3 : Entails.eval a c7799 := derived7799 a h
  have h4 : Entails.eval a c7757 := derived7757 a h
  have h5 : Entails.eval a c7697 := derived7697 a h
  have h6 : Entails.eval a c7639 := derived7639 a h
  have h7 : Entails.eval a c2067 := h 2066 (by decide)
  have h8 : Entails.eval a c7698 := derived7698 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7814 : DefaultClause 65 := directClause [(⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7814 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7714, some c7626, some c7470, some c7764, some c7789, some c7793, some c7795, some c7803, some c7805, some c7812, some c7813, some c1125, some c1126, some c1134, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7814 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7814 : lratChecker f7814 p7814 = .success := by decide +kernel
theorem unsat7814 : Unsatisfiable (PosFin 65) f7814 := by
  apply lratCheckerSound f7814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7814
  · intro a ha; simp [p7814] at ha; subst a; trivial
  · exact checked7814
theorem derived7814 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7814 := by
  apply localUnsat_implies_entails f7814 [c7714, c7626, c7470, c7764, c7789, c7793, c7795, c7803, c7805, c7812, c7813, c1125, c1126, c1134] c7814 unsat7814 (by rfl) a
  have h0 : Entails.eval a c7714 := derived7714 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7470 := derived7470 a h
  have h3 : Entails.eval a c7764 := derived7764 a h
  have h4 : Entails.eval a c7789 := derived7789 a h
  have h5 : Entails.eval a c7793 := derived7793 a h
  have h6 : Entails.eval a c7795 := derived7795 a h
  have h7 : Entails.eval a c7803 := derived7803 a h
  have h8 : Entails.eval a c7805 := derived7805 a h
  have h9 : Entails.eval a c7812 := derived7812 a h
  have h10 : Entails.eval a c7813 := derived7813 a h
  have h11 : Entails.eval a c1125 := h 1124 (by decide)
  have h12 : Entails.eval a c1126 := h 1125 (by decide)
  have h13 : Entails.eval a c1134 := h 1133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7815 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7815 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c347, some c354, some c342, some c332, some c367, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7815 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7815 : lratChecker f7815 p7815 = .success := by decide +kernel
theorem unsat7815 : Unsatisfiable (PosFin 65) f7815 := by
  apply lratCheckerSound f7815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7815
  · intro a ha; simp [p7815] at ha; subst a; trivial
  · exact checked7815
theorem derived7815 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7815 := by
  apply localUnsat_implies_entails f7815 [c347, c354, c342, c332, c367] c7815 unsat7815 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  have h3 : Entails.eval a c332 := h 331 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7816 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7816 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c711, some c769, some c1434, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7816 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7816 : lratChecker f7816 p7816 = .success := by decide +kernel
theorem unsat7816 : Unsatisfiable (PosFin 65) f7816 := by
  apply lratCheckerSound f7816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7816
  · intro a ha; simp [p7816] at ha; subst a; trivial
  · exact checked7816
theorem derived7816 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7816 := by
  apply localUnsat_implies_entails f7816 [c711, c769, c1434] c7816 unsat7816 (by rfl) a
  have h0 : Entails.eval a c711 := h 710 (by decide)
  have h1 : Entails.eval a c769 := h 768 (by decide)
  have h2 : Entails.eval a c1434 := h 1433 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7817 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨30, by decide⟩, true), (⟨17, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7817 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1438, some c1412, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7817 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7817 : lratChecker f7817 p7817 = .success := by decide +kernel
theorem unsat7817 : Unsatisfiable (PosFin 65) f7817 := by
  apply lratCheckerSound f7817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7817
  · intro a ha; simp [p7817] at ha; subst a; trivial
  · exact checked7817
theorem derived7817 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7817 := by
  apply localUnsat_implies_entails f7817 [c1438, c1412] c7817 unsat7817 (by rfl) a
  have h0 : Entails.eval a c1438 := h 1437 (by decide)
  have h1 : Entails.eval a c1412 := h 1411 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7818 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7818 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c694, some c707, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7818 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7818 : lratChecker f7818 p7818 = .success := by decide +kernel
theorem unsat7818 : Unsatisfiable (PosFin 65) f7818 := by
  apply lratCheckerSound f7818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7818
  · intro a ha; simp [p7818] at ha; subst a; trivial
  · exact checked7818
theorem derived7818 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7818 := by
  apply localUnsat_implies_entails f7818 [c694, c707] c7818 unsat7818 (by rfl) a
  have h0 : Entails.eval a c694 := h 693 (by decide)
  have h1 : Entails.eval a c707 := h 706 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7819 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7819 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7753, some c1438, some c1450, some c1413, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7819 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7819 : lratChecker f7819 p7819 = .success := by decide +kernel
theorem unsat7819 : Unsatisfiable (PosFin 65) f7819 := by
  apply lratCheckerSound f7819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7819
  · intro a ha; simp [p7819] at ha; subst a; trivial
  · exact checked7819
theorem derived7819 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7819 := by
  apply localUnsat_implies_entails f7819 [c7753, c1438, c1450, c1413] c7819 unsat7819 (by rfl) a
  have h0 : Entails.eval a c7753 := derived7753 a h
  have h1 : Entails.eval a c1438 := h 1437 (by decide)
  have h2 : Entails.eval a c1450 := h 1449 (by decide)
  have h3 : Entails.eval a c1413 := h 1412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7820 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7820 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c747, some c764, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7820 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7820 : lratChecker f7820 p7820 = .success := by decide +kernel
theorem unsat7820 : Unsatisfiable (PosFin 65) f7820 := by
  apply lratCheckerSound f7820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7820
  · intro a ha; simp [p7820] at ha; subst a; trivial
  · exact checked7820
theorem derived7820 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7820 := by
  apply localUnsat_implies_entails f7820 [c747, c764] c7820 unsat7820 (by rfl) a
  have h0 : Entails.eval a c747 := h 746 (by decide)
  have h1 : Entails.eval a c764 := h 763 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7821 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7821 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7815, some c7816, some c7818, some c7820, some c1438, some c7819, some c1421, some c7697, some c1447, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7821 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7821 : lratChecker f7821 p7821 = .success := by decide +kernel
theorem unsat7821 : Unsatisfiable (PosFin 65) f7821 := by
  apply lratCheckerSound f7821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7821
  · intro a ha; simp [p7821] at ha; subst a; trivial
  · exact checked7821
theorem derived7821 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7821 := by
  apply localUnsat_implies_entails f7821 [c7815, c7816, c7818, c7820, c1438, c7819, c1421, c7697, c1447] c7821 unsat7821 (by rfl) a
  have h0 : Entails.eval a c7815 := derived7815 a h
  have h1 : Entails.eval a c7816 := derived7816 a h
  have h2 : Entails.eval a c7818 := derived7818 a h
  have h3 : Entails.eval a c7820 := derived7820 a h
  have h4 : Entails.eval a c1438 := h 1437 (by decide)
  have h5 : Entails.eval a c7819 := derived7819 a h
  have h6 : Entails.eval a c1421 := h 1420 (by decide)
  have h7 : Entails.eval a c7697 := derived7697 a h
  have h8 : Entails.eval a c1447 := h 1446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7822 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7822 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c347, some c354, some c332, some c367, some c357, some c345, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7822 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7822 : lratChecker f7822 p7822 = .success := by decide +kernel
theorem unsat7822 : Unsatisfiable (PosFin 65) f7822 := by
  apply lratCheckerSound f7822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7822
  · intro a ha; simp [p7822] at ha; subst a; trivial
  · exact checked7822
theorem derived7822 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7822 := by
  apply localUnsat_implies_entails f7822 [c347, c354, c332, c367, c357, c345] c7822 unsat7822 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c332 := h 331 (by decide)
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7823 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7823 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c773, some c7638, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7823 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7823 : lratChecker f7823 p7823 = .success := by decide +kernel
theorem unsat7823 : Unsatisfiable (PosFin 65) f7823 := by
  apply lratCheckerSound f7823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7823
  · intro a ha; simp [p7823] at ha; subst a; trivial
  · exact checked7823
theorem derived7823 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7823 := by
  apply localUnsat_implies_entails f7823 [c773, c7638] c7823 unsat7823 (by rfl) a
  have h0 : Entails.eval a c773 := h 772 (by decide)
  have h1 : Entails.eval a c7638 := derived7638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7824 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7824 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c714, some c723, some c707, some c704, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7824 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7824 : lratChecker f7824 p7824 = .success := by decide +kernel
theorem unsat7824 : Unsatisfiable (PosFin 65) f7824 := by
  apply lratCheckerSound f7824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7824
  · intro a ha; simp [p7824] at ha; subst a; trivial
  · exact checked7824
theorem derived7824 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7824 := by
  apply localUnsat_implies_entails f7824 [c714, c723, c707, c704] c7824 unsat7824 (by rfl) a
  have h0 : Entails.eval a c714 := h 713 (by decide)
  have h1 : Entails.eval a c723 := h 722 (by decide)
  have h2 : Entails.eval a c707 := h 706 (by decide)
  have h3 : Entails.eval a c704 := h 703 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7825 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7825 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7821, some c7822, some c7816, some c7823, some c7824, some c7819, some c1438, some c7697, some c1421, some c1447, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7825 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7825 : lratChecker f7825 p7825 = .success := by decide +kernel
theorem unsat7825 : Unsatisfiable (PosFin 65) f7825 := by
  apply lratCheckerSound f7825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7825
  · intro a ha; simp [p7825] at ha; subst a; trivial
  · exact checked7825
theorem derived7825 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7825 := by
  apply localUnsat_implies_entails f7825 [c7821, c7822, c7816, c7823, c7824, c7819, c1438, c7697, c1421, c1447] c7825 unsat7825 (by rfl) a
  have h0 : Entails.eval a c7821 := derived7821 a h
  have h1 : Entails.eval a c7822 := derived7822 a h
  have h2 : Entails.eval a c7816 := derived7816 a h
  have h3 : Entails.eval a c7823 := derived7823 a h
  have h4 : Entails.eval a c7824 := derived7824 a h
  have h5 : Entails.eval a c7819 := derived7819 a h
  have h6 : Entails.eval a c1438 := h 1437 (by decide)
  have h7 : Entails.eval a c7697 := derived7697 a h
  have h8 : Entails.eval a c1421 := h 1420 (by decide)
  have h9 : Entails.eval a c1447 := h 1446 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7826 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7826 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c397, some c1127, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7826 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7826 : lratChecker f7826 p7826 = .success := by decide +kernel
theorem unsat7826 : Unsatisfiable (PosFin 65) f7826 := by
  apply lratCheckerSound f7826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7826
  · intro a ha; simp [p7826] at ha; subst a; trivial
  · exact checked7826
theorem derived7826 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7826 := by
  apply localUnsat_implies_entails f7826 [c397, c1127] c7826 unsat7826 (by rfl) a
  have h0 : Entails.eval a c397 := h 396 (by decide)
  have h1 : Entails.eval a c1127 := h 1126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7827 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7827 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1132, some c1142, some c1109, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7827 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7827 : lratChecker f7827 p7827 = .success := by decide +kernel
theorem unsat7827 : Unsatisfiable (PosFin 65) f7827 := by
  apply lratCheckerSound f7827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7827
  · intro a ha; simp [p7827] at ha; subst a; trivial
  · exact checked7827
theorem derived7827 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7827 := by
  apply localUnsat_implies_entails f7827 [c1132, c1142, c1109] c7827 unsat7827 (by rfl) a
  have h0 : Entails.eval a c1132 := h 1131 (by decide)
  have h1 : Entails.eval a c1142 := h 1141 (by decide)
  have h2 : Entails.eval a c1109 := h 1108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7828 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7828 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7814, some c7825, some c7766, some c7827, some c417, some c403, some c381, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7828 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7828 : lratChecker f7828 p7828 = .success := by decide +kernel
theorem unsat7828 : Unsatisfiable (PosFin 65) f7828 := by
  apply lratCheckerSound f7828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7828
  · intro a ha; simp [p7828] at ha; subst a; trivial
  · exact checked7828
theorem derived7828 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7828 := by
  apply localUnsat_implies_entails f7828 [c7470, c7626, c7714, c7814, c7825, c7766, c7827, c417, c403, c381] c7828 unsat7828 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7814 := derived7814 a h
  have h4 : Entails.eval a c7825 := derived7825 a h
  have h5 : Entails.eval a c7766 := derived7766 a h
  have h6 : Entails.eval a c7827 := derived7827 a h
  have h7 : Entails.eval a c417 := h 416 (by decide)
  have h8 : Entails.eval a c403 := h 402 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7829 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7829 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7814, some c7825, some c7826, some c7828, some c7791, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7829 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7829 : lratChecker f7829 p7829 = .success := by decide +kernel
theorem unsat7829 : Unsatisfiable (PosFin 65) f7829 := by
  apply lratCheckerSound f7829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7829
  · intro a ha; simp [p7829] at ha; subst a; trivial
  · exact checked7829
theorem derived7829 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7829 := by
  apply localUnsat_implies_entails f7829 [c7470, c7626, c7714, c7814, c7825, c7826, c7828, c7791] c7829 unsat7829 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7814 := derived7814 a h
  have h4 : Entails.eval a c7825 := derived7825 a h
  have h5 : Entails.eval a c7826 := derived7826 a h
  have h6 : Entails.eval a c7828 := derived7828 a h
  have h7 : Entails.eval a c7791 := derived7791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7830 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7830 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c817, some c808, some c788, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7830 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7830 : lratChecker f7830 p7830 = .success := by decide +kernel
theorem unsat7830 : Unsatisfiable (PosFin 65) f7830 := by
  apply lratCheckerSound f7830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7830
  · intro a ha; simp [p7830] at ha; subst a; trivial
  · exact checked7830
theorem derived7830 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7830 := by
  apply localUnsat_implies_entails f7830 [c817, c808, c788] c7830 unsat7830 (by rfl) a
  have h0 : Entails.eval a c817 := h 816 (by decide)
  have h1 : Entails.eval a c808 := h 807 (by decide)
  have h2 : Entails.eval a c788 := h 787 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7831 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7831 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7814, some c7825, some c7766, some c7827, some c7830, some c7819, some c739, some c725, some c729, some c734, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7831 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7831 : lratChecker f7831 p7831 = .success := by decide +kernel
theorem unsat7831 : Unsatisfiable (PosFin 65) f7831 := by
  apply lratCheckerSound f7831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7831
  · intro a ha; simp [p7831] at ha; subst a; trivial
  · exact checked7831
theorem derived7831 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7831 := by
  apply localUnsat_implies_entails f7831 [c7470, c7626, c7714, c7814, c7825, c7766, c7827, c7830, c7819, c739, c725, c729, c734] c7831 unsat7831 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7814 := derived7814 a h
  have h4 : Entails.eval a c7825 := derived7825 a h
  have h5 : Entails.eval a c7766 := derived7766 a h
  have h6 : Entails.eval a c7827 := derived7827 a h
  have h7 : Entails.eval a c7830 := derived7830 a h
  have h8 : Entails.eval a c7819 := derived7819 a h
  have h9 : Entails.eval a c739 := h 738 (by decide)
  have h10 : Entails.eval a c725 := h 724 (by decide)
  have h11 : Entails.eval a c729 := h 728 (by decide)
  have h12 : Entails.eval a c734 := h 733 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7832 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7832 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7814, some c7825, some c7829, some c7831, some c7791, some c875, some c1127, some c913, some c1917, some c805, some c1358, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7832 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7832 : lratChecker f7832 p7832 = .success := by decide +kernel
theorem unsat7832 : Unsatisfiable (PosFin 65) f7832 := by
  apply lratCheckerSound f7832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7832
  · intro a ha; simp [p7832] at ha; subst a; trivial
  · exact checked7832
theorem derived7832 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7832 := by
  apply localUnsat_implies_entails f7832 [c7470, c7626, c7714, c7814, c7825, c7829, c7831, c7791, c875, c1127, c913, c1917, c805, c1358] c7832 unsat7832 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7814 := derived7814 a h
  have h4 : Entails.eval a c7825 := derived7825 a h
  have h5 : Entails.eval a c7829 := derived7829 a h
  have h6 : Entails.eval a c7831 := derived7831 a h
  have h7 : Entails.eval a c7791 := derived7791 a h
  have h8 : Entails.eval a c875 := h 874 (by decide)
  have h9 : Entails.eval a c1127 := h 1126 (by decide)
  have h10 : Entails.eval a c913 := h 912 (by decide)
  have h11 : Entails.eval a c1917 := h 1916 (by decide)
  have h12 : Entails.eval a c805 := h 804 (by decide)
  have h13 : Entails.eval a c1358 := h 1357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7833 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7833 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7337, some c306, some c290, some c291, some c310, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p7833 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7833 : lratChecker f7833 p7833 = .success := by decide +kernel
theorem unsat7833 : Unsatisfiable (PosFin 65) f7833 := by
  apply lratCheckerSound f7833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7833
  · intro a ha; simp [p7833] at ha; subst a; trivial
  · exact checked7833
theorem derived7833 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7833 := by
  apply localUnsat_implies_entails f7833 [c7337, c306, c290, c291, c310] c7833 unsat7833 (by rfl) a
  have h0 : Entails.eval a c7337 := derived7337 a h
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7834 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7834 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c805, some c808, some c804, some c788, some c811, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7834 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7834 : lratChecker f7834 p7834 = .success := by decide +kernel
theorem unsat7834 : Unsatisfiable (PosFin 65) f7834 := by
  apply lratCheckerSound f7834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7834
  · intro a ha; simp [p7834] at ha; subst a; trivial
  · exact checked7834
theorem derived7834 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7834 := by
  apply localUnsat_implies_entails f7834 [c805, c808, c804, c788, c811] c7834 unsat7834 (by rfl) a
  have h0 : Entails.eval a c805 := h 804 (by decide)
  have h1 : Entails.eval a c808 := h 807 (by decide)
  have h2 : Entails.eval a c804 := h 803 (by decide)
  have h3 : Entails.eval a c788 := h 787 (by decide)
  have h4 : Entails.eval a c811 := h 810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7835 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7835 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1127, some c1125, some c1126, some c1140, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7835 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7835 : lratChecker f7835 p7835 = .success := by decide +kernel
theorem unsat7835 : Unsatisfiable (PosFin 65) f7835 := by
  apply lratCheckerSound f7835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7835
  · intro a ha; simp [p7835] at ha; subst a; trivial
  · exact checked7835
theorem derived7835 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7835 := by
  apply localUnsat_implies_entails f7835 [c1127, c1125, c1126, c1140] c7835 unsat7835 (by rfl) a
  have h0 : Entails.eval a c1127 := h 1126 (by decide)
  have h1 : Entails.eval a c1125 := h 1124 (by decide)
  have h2 : Entails.eval a c1126 := h 1125 (by decide)
  have h3 : Entails.eval a c1140 := h 1139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7836 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7836 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c875, some c913, some c1917, some c1358, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p7836 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7836 : lratChecker f7836 p7836 = .success := by decide +kernel
theorem unsat7836 : Unsatisfiable (PosFin 65) f7836 := by
  apply lratCheckerSound f7836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7836
  · intro a ha; simp [p7836] at ha; subst a; trivial
  · exact checked7836
theorem derived7836 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7836 := by
  apply localUnsat_implies_entails f7836 [c875, c913, c1917, c1358] c7836 unsat7836 (by rfl) a
  have h0 : Entails.eval a c875 := h 874 (by decide)
  have h1 : Entails.eval a c913 := h 912 (by decide)
  have h2 : Entails.eval a c1917 := h 1916 (by decide)
  have h3 : Entails.eval a c1358 := h 1357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7837 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7837 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7814, some c7714, some c7626, some c7470, some c7825, some c7832, some c7833, some c7831, some c7835, some c7834, some c7836, some c7697, some c7639, some c7698, some c743, some c2123, some c1438, some c1421, some c1420, some c2606, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7837 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked7837 : lratChecker f7837 p7837 = .success := by decide +kernel
theorem unsat7837 : Unsatisfiable (PosFin 65) f7837 := by
  apply lratCheckerSound f7837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7837
  · intro a ha; simp [p7837] at ha; subst a; trivial
  · exact checked7837
theorem derived7837 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7837 := by
  apply localUnsat_implies_entails f7837 [c7814, c7714, c7626, c7470, c7825, c7832, c7833, c7831, c7835, c7834, c7836, c7697, c7639, c7698, c743, c2123, c1438, c1421, c1420, c2606] c7837 unsat7837 (by rfl) a
  have h0 : Entails.eval a c7814 := derived7814 a h
  have h1 : Entails.eval a c7714 := derived7714 a h
  have h2 : Entails.eval a c7626 := derived7626 a h
  have h3 : Entails.eval a c7470 := derived7470 a h
  have h4 : Entails.eval a c7825 := derived7825 a h
  have h5 : Entails.eval a c7832 := derived7832 a h
  have h6 : Entails.eval a c7833 := derived7833 a h
  have h7 : Entails.eval a c7831 := derived7831 a h
  have h8 : Entails.eval a c7835 := derived7835 a h
  have h9 : Entails.eval a c7834 := derived7834 a h
  have h10 : Entails.eval a c7836 := derived7836 a h
  have h11 : Entails.eval a c7697 := derived7697 a h
  have h12 : Entails.eval a c7639 := derived7639 a h
  have h13 : Entails.eval a c7698 := derived7698 a h
  have h14 : Entails.eval a c743 := h 742 (by decide)
  have h15 : Entails.eval a c2123 := h 2122 (by decide)
  have h16 : Entails.eval a c1438 := h 1437 (by decide)
  have h17 : Entails.eval a c1421 := h 1420 (by decide)
  have h18 : Entails.eval a c1420 := h 1419 (by decide)
  have h19 : Entails.eval a c2606 := h 2605 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7838 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7838 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7815, some c7822, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7838 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7838 : lratChecker f7838 p7838 = .success := by decide +kernel
theorem unsat7838 : Unsatisfiable (PosFin 65) f7838 := by
  apply lratCheckerSound f7838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7838
  · intro a ha; simp [p7838] at ha; subst a; trivial
  · exact checked7838
theorem derived7838 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7838 := by
  apply localUnsat_implies_entails f7838 [c7815, c7822] c7838 unsat7838 (by rfl) a
  have h0 : Entails.eval a c7815 := derived7815 a h
  have h1 : Entails.eval a c7822 := derived7822 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7839 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7839 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c756, some c783, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7839 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7839 : lratChecker f7839 p7839 = .success := by decide +kernel
theorem unsat7839 : Unsatisfiable (PosFin 65) f7839 := by
  apply lratCheckerSound f7839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7839
  · intro a ha; simp [p7839] at ha; subst a; trivial
  · exact checked7839
theorem derived7839 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7839 := by
  apply localUnsat_implies_entails f7839 [c756, c783] c7839 unsat7839 (by rfl) a
  have h0 : Entails.eval a c756 := h 755 (by decide)
  have h1 : Entails.eval a c783 := h 782 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7840 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7840 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1427, some c700, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7840 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7840 : lratChecker f7840 p7840 = .success := by decide +kernel
theorem unsat7840 : Unsatisfiable (PosFin 65) f7840 := by
  apply lratCheckerSound f7840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7840
  · intro a ha; simp [p7840] at ha; subst a; trivial
  · exact checked7840
theorem derived7840 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7840 := by
  apply localUnsat_implies_entails f7840 [c1427, c700] c7840 unsat7840 (by rfl) a
  have h0 : Entails.eval a c1427 := h 1426 (by decide)
  have h1 : Entails.eval a c700 := h 699 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7841 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7841 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7839, some c7840, some c891, some c930, some c1370, some c1923, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7841 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7841 : lratChecker f7841 p7841 = .success := by decide +kernel
theorem unsat7841 : Unsatisfiable (PosFin 65) f7841 := by
  apply lratCheckerSound f7841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7841
  · intro a ha; simp [p7841] at ha; subst a; trivial
  · exact checked7841
theorem derived7841 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7841 := by
  apply localUnsat_implies_entails f7841 [c7839, c7840, c891, c930, c1370, c1923] c7841 unsat7841 (by rfl) a
  have h0 : Entails.eval a c7839 := derived7839 a h
  have h1 : Entails.eval a c7840 := derived7840 a h
  have h2 : Entails.eval a c891 := h 890 (by decide)
  have h3 : Entails.eval a c930 := h 929 (by decide)
  have h4 : Entails.eval a c1370 := h 1369 (by decide)
  have h5 : Entails.eval a c1923 := h 1922 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7842 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨20, by decide⟩, true), (⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7842 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c756, some c768, some c782, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7842 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7842 : lratChecker f7842 p7842 = .success := by decide +kernel
theorem unsat7842 : Unsatisfiable (PosFin 65) f7842 := by
  apply lratCheckerSound f7842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7842
  · intro a ha; simp [p7842] at ha; subst a; trivial
  · exact checked7842
theorem derived7842 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7842 := by
  apply localUnsat_implies_entails f7842 [c756, c768, c782] c7842 unsat7842 (by rfl) a
  have h0 : Entails.eval a c756 := h 755 (by decide)
  have h1 : Entails.eval a c768 := h 767 (by decide)
  have h2 : Entails.eval a c782 := h 781 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7843 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7843 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7838, some c7816, some c7841, some c7842, some c7697, some c7840, some c1447, some c722, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7843 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7843 : lratChecker f7843 p7843 = .success := by decide +kernel
theorem unsat7843 : Unsatisfiable (PosFin 65) f7843 := by
  apply lratCheckerSound f7843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7843
  · intro a ha; simp [p7843] at ha; subst a; trivial
  · exact checked7843
theorem derived7843 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7843 := by
  apply localUnsat_implies_entails f7843 [c7838, c7816, c7841, c7842, c7697, c7840, c1447, c722] c7843 unsat7843 (by rfl) a
  have h0 : Entails.eval a c7838 := derived7838 a h
  have h1 : Entails.eval a c7816 := derived7816 a h
  have h2 : Entails.eval a c7841 := derived7841 a h
  have h3 : Entails.eval a c7842 := derived7842 a h
  have h4 : Entails.eval a c7697 := derived7697 a h
  have h5 : Entails.eval a c7840 := derived7840 a h
  have h6 : Entails.eval a c1447 := h 1446 (by decide)
  have h7 : Entails.eval a c722 := h 721 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7844 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7844 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7814, some c7837, some c7843, some c7833, some c7767, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7844 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7844 : lratChecker f7844 p7844 = .success := by decide +kernel
theorem unsat7844 : Unsatisfiable (PosFin 65) f7844 := by
  apply lratCheckerSound f7844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7844
  · intro a ha; simp [p7844] at ha; subst a; trivial
  · exact checked7844
theorem derived7844 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7844 := by
  apply localUnsat_implies_entails f7844 [c7470, c7626, c7714, c7814, c7837, c7843, c7833, c7767] c7844 unsat7844 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7814 := derived7814 a h
  have h4 : Entails.eval a c7837 := derived7837 a h
  have h5 : Entails.eval a c7843 := derived7843 a h
  have h6 : Entails.eval a c7833 := derived7833 a h
  have h7 : Entails.eval a c7767 := derived7767 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7845 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7845 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7830, some c1127, some c1132, some c1142, some c7827, some c2622, some c7716, some c2546, some c2362, some c2526, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7845 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7845 : lratChecker f7845 p7845 = .success := by decide +kernel
theorem unsat7845 : Unsatisfiable (PosFin 65) f7845 := by
  apply lratCheckerSound f7845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7845
  · intro a ha; simp [p7845] at ha; subst a; trivial
  · exact checked7845
theorem derived7845 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7845 := by
  apply localUnsat_implies_entails f7845 [c7830, c1127, c1132, c1142, c7827, c2622, c7716, c2546, c2362, c2526] c7845 unsat7845 (by rfl) a
  have h0 : Entails.eval a c7830 := derived7830 a h
  have h1 : Entails.eval a c1127 := h 1126 (by decide)
  have h2 : Entails.eval a c1132 := h 1131 (by decide)
  have h3 : Entails.eval a c1142 := h 1141 (by decide)
  have h4 : Entails.eval a c7827 := derived7827 a h
  have h5 : Entails.eval a c2622 := h 2621 (by decide)
  have h6 : Entails.eval a c7716 := derived7716 a h
  have h7 : Entails.eval a c2546 := h 2545 (by decide)
  have h8 : Entails.eval a c2362 := h 2361 (by decide)
  have h9 : Entails.eval a c2526 := h 2525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7846 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨12, by decide⟩, true), (⟨27, by decide⟩, true), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7846 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1427, some c1288, some c1353, some c1968, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7846 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7846 : lratChecker f7846 p7846 = .success := by decide +kernel
theorem unsat7846 : Unsatisfiable (PosFin 65) f7846 := by
  apply lratCheckerSound f7846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7846
  · intro a ha; simp [p7846] at ha; subst a; trivial
  · exact checked7846
theorem derived7846 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7846 := by
  apply localUnsat_implies_entails f7846 [c1427, c1288, c1353, c1968] c7846 unsat7846 (by rfl) a
  have h0 : Entails.eval a c1427 := h 1426 (by decide)
  have h1 : Entails.eval a c1288 := h 1287 (by decide)
  have h2 : Entails.eval a c1353 := h 1352 (by decide)
  have h3 : Entails.eval a c1968 := h 1967 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7847 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7847 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7843, some c7845, some c7846, some c891, some c1142, some c1076, some c2039, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p7847 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7847 : lratChecker f7847 p7847 = .success := by decide +kernel
theorem unsat7847 : Unsatisfiable (PosFin 65) f7847 := by
  apply lratCheckerSound f7847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7847
  · intro a ha; simp [p7847] at ha; subst a; trivial
  · exact checked7847
theorem derived7847 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7847 := by
  apply localUnsat_implies_entails f7847 [c7843, c7845, c7846, c891, c1142, c1076, c2039] c7847 unsat7847 (by rfl) a
  have h0 : Entails.eval a c7843 := derived7843 a h
  have h1 : Entails.eval a c7845 := derived7845 a h
  have h2 : Entails.eval a c7846 := derived7846 a h
  have h3 : Entails.eval a c891 := h 890 (by decide)
  have h4 : Entails.eval a c1142 := h 1141 (by decide)
  have h5 : Entails.eval a c1076 := h 1075 (by decide)
  have h6 : Entails.eval a c2039 := h 2038 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7848 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7848 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7834, some c805, some c802, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p7848 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7848 : lratChecker f7848 p7848 = .success := by decide +kernel
theorem unsat7848 : Unsatisfiable (PosFin 65) f7848 := by
  apply lratCheckerSound f7848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7848
  · intro a ha; simp [p7848] at ha; subst a; trivial
  · exact checked7848
theorem derived7848 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7848 := by
  apply localUnsat_implies_entails f7848 [c7834, c805, c802] c7848 unsat7848 (by rfl) a
  have h0 : Entails.eval a c7834 := derived7834 a h
  have h1 : Entails.eval a c805 := h 804 (by decide)
  have h2 : Entails.eval a c802 := h 801 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7849 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7849 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7470, some c7626, some c7714, some c7814, some c7837, some c7843, some c7844, some c7847, some c7835, some c7848, some c7836, some c7697, some c7846, some c1447, some c744, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7849 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7849 : lratChecker f7849 p7849 = .success := by decide +kernel
theorem unsat7849 : Unsatisfiable (PosFin 65) f7849 := by
  apply lratCheckerSound f7849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7849
  · intro a ha; simp [p7849] at ha; subst a; trivial
  · exact checked7849
theorem derived7849 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7849 := by
  apply localUnsat_implies_entails f7849 [c7470, c7626, c7714, c7814, c7837, c7843, c7844, c7847, c7835, c7848, c7836, c7697, c7846, c1447, c744] c7849 unsat7849 (by rfl) a
  have h0 : Entails.eval a c7470 := derived7470 a h
  have h1 : Entails.eval a c7626 := derived7626 a h
  have h2 : Entails.eval a c7714 := derived7714 a h
  have h3 : Entails.eval a c7814 := derived7814 a h
  have h4 : Entails.eval a c7837 := derived7837 a h
  have h5 : Entails.eval a c7843 := derived7843 a h
  have h6 : Entails.eval a c7844 := derived7844 a h
  have h7 : Entails.eval a c7847 := derived7847 a h
  have h8 : Entails.eval a c7835 := derived7835 a h
  have h9 : Entails.eval a c7848 := derived7848 a h
  have h10 : Entails.eval a c7836 := derived7836 a h
  have h11 : Entails.eval a c7697 := derived7697 a h
  have h12 : Entails.eval a c7846 := derived7846 a h
  have h13 : Entails.eval a c1447 := h 1446 (by decide)
  have h14 : Entails.eval a c744 := h 743 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7850 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7850 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c6670, some c2943, some c114, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7850 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7850 : lratChecker f7850 p7850 = .success := by decide +kernel
theorem unsat7850 : Unsatisfiable (PosFin 65) f7850 := by
  apply lratCheckerSound f7850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7850
  · intro a ha; simp [p7850] at ha; subst a; trivial
  · exact checked7850
theorem derived7850 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7850 := by
  apply localUnsat_implies_entails f7850 [c6670, c2943, c114] c7850 unsat7850 (by rfl) a
  have h0 : Entails.eval a c6670 := derived6670 a h
  have h1 : Entails.eval a c2943 := h 2942 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7851 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨30, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7851 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c1171, some c1199, some c7481, some c825, some c7850, some c28, some c29, some c2950, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7851 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7851 : lratChecker f7851 p7851 = .success := by decide +kernel
theorem unsat7851 : Unsatisfiable (PosFin 65) f7851 := by
  apply lratCheckerSound f7851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7851
  · intro a ha; simp [p7851] at ha; subst a; trivial
  · exact checked7851
theorem derived7851 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7851 := by
  apply localUnsat_implies_entails f7851 [c7849, c1171, c1199, c7481, c825, c7850, c28, c29, c2950] c7851 unsat7851 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c1171 := h 1170 (by decide)
  have h2 : Entails.eval a c1199 := h 1198 (by decide)
  have h3 : Entails.eval a c7481 := derived7481 a h
  have h4 : Entails.eval a c825 := h 824 (by decide)
  have h5 : Entails.eval a c7850 := derived7850 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c2950 := h 2949 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7852 : DefaultClause 65 := directClause [(⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨30, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7852 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7851, some c1176, some c1201, some c7765, some c825, some c28, some c29, some c2895, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7852 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7852 : lratChecker f7852 p7852 = .success := by decide +kernel
theorem unsat7852 : Unsatisfiable (PosFin 65) f7852 := by
  apply lratCheckerSound f7852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7852
  · intro a ha; simp [p7852] at ha; subst a; trivial
  · exact checked7852
theorem derived7852 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7852 := by
  apply localUnsat_implies_entails f7852 [c7849, c7851, c1176, c1201, c7765, c825, c28, c29, c2895] c7852 unsat7852 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7851 := derived7851 a h
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  have h3 : Entails.eval a c1201 := h 1200 (by decide)
  have h4 : Entails.eval a c7765 := derived7765 a h
  have h5 : Entails.eval a c825 := h 824 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c2895 := h 2894 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7853 : DefaultClause 65 := directClause [(⟨21, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7853 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2308, some c1184, some c505, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7853 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7853 : lratChecker f7853 p7853 = .success := by decide +kernel
theorem unsat7853 : Unsatisfiable (PosFin 65) f7853 := by
  apply lratCheckerSound f7853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7853
  · intro a ha; simp [p7853] at ha; subst a; trivial
  · exact checked7853
theorem derived7853 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7853 := by
  apply localUnsat_implies_entails f7853 [c2308, c1184, c505] c7853 unsat7853 (by rfl) a
  have h0 : Entails.eval a c2308 := h 2307 (by decide)
  have h1 : Entails.eval a c1184 := h 1183 (by decide)
  have h2 : Entails.eval a c505 := h 504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7854 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7854 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1199, some c1383, some c2503, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7854 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7854 : lratChecker f7854 p7854 = .success := by decide +kernel
theorem unsat7854 : Unsatisfiable (PosFin 65) f7854 := by
  apply lratCheckerSound f7854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7854
  · intro a ha; simp [p7854] at ha; subst a; trivial
  · exact checked7854
theorem derived7854 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7854 := by
  apply localUnsat_implies_entails f7854 [c1199, c1383, c2503] c7854 unsat7854 (by rfl) a
  have h0 : Entails.eval a c1199 := h 1198 (by decide)
  have h1 : Entails.eval a c1383 := h 1382 (by decide)
  have h2 : Entails.eval a c2503 := h 2502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7855 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7855 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7854, some c1201, some c1381, some c2500, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7855 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7855 : lratChecker f7855 p7855 = .success := by decide +kernel
theorem unsat7855 : Unsatisfiable (PosFin 65) f7855 := by
  apply lratCheckerSound f7855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7855
  · intro a ha; simp [p7855] at ha; subst a; trivial
  · exact checked7855
theorem derived7855 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7855 := by
  apply localUnsat_implies_entails f7855 [c7854, c1201, c1381, c2500] c7855 unsat7855 (by rfl) a
  have h0 : Entails.eval a c7854 := derived7854 a h
  have h1 : Entails.eval a c1201 := h 1200 (by decide)
  have h2 : Entails.eval a c1381 := h 1380 (by decide)
  have h3 : Entails.eval a c2500 := h 2499 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7856 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7856 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c2289, some c2350, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7856 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7856 : lratChecker f7856 p7856 = .success := by decide +kernel
theorem unsat7856 : Unsatisfiable (PosFin 65) f7856 := by
  apply lratCheckerSound f7856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7856
  · intro a ha; simp [p7856] at ha; subst a; trivial
  · exact checked7856
theorem derived7856 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7856 := by
  apply localUnsat_implies_entails f7856 [c1171, c2289, c2350] c7856 unsat7856 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c2289 := h 2288 (by decide)
  have h2 : Entails.eval a c2350 := h 2349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7857 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7857 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7853, some c7852, some c7855, some c7856, some c1176, some c2280, some c2348, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7857 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7857 : lratChecker f7857 p7857 = .success := by decide +kernel
theorem unsat7857 : Unsatisfiable (PosFin 65) f7857 := by
  apply lratCheckerSound f7857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7857
  · intro a ha; simp [p7857] at ha; subst a; trivial
  · exact checked7857
theorem derived7857 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7857 := by
  apply localUnsat_implies_entails f7857 [c7849, c7853, c7852, c7855, c7856, c1176, c2280, c2348] c7857 unsat7857 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7853 := derived7853 a h
  have h2 : Entails.eval a c7852 := derived7852 a h
  have h3 : Entails.eval a c7855 := derived7855 a h
  have h4 : Entails.eval a c7856 := derived7856 a h
  have h5 : Entails.eval a c1176 := h 1175 (by decide)
  have h6 : Entails.eval a c2280 := h 2279 (by decide)
  have h7 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7858 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7858 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c1199, some c2060, some c821, some c463, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7858 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7858 : lratChecker f7858 p7858 = .success := by decide +kernel
theorem unsat7858 : Unsatisfiable (PosFin 65) f7858 := by
  apply lratCheckerSound f7858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7858
  · intro a ha; simp [p7858] at ha; subst a; trivial
  · exact checked7858
theorem derived7858 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7858 := by
  apply localUnsat_implies_entails f7858 [c1171, c1199, c2060, c821, c463] c7858 unsat7858 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c1199 := h 1198 (by decide)
  have h2 : Entails.eval a c2060 := h 2059 (by decide)
  have h3 : Entails.eval a c821 := h 820 (by decide)
  have h4 : Entails.eval a c463 := h 462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7859 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7859 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7858, some c1176, some c1201, some c2056, some c821, some c463, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7859 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7859 : lratChecker f7859 p7859 = .success := by decide +kernel
theorem unsat7859 : Unsatisfiable (PosFin 65) f7859 := by
  apply lratCheckerSound f7859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7859
  · intro a ha; simp [p7859] at ha; subst a; trivial
  · exact checked7859
theorem derived7859 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7859 := by
  apply localUnsat_implies_entails f7859 [c7858, c1176, c1201, c2056, c821, c463] c7859 unsat7859 (by rfl) a
  have h0 : Entails.eval a c7858 := derived7858 a h
  have h1 : Entails.eval a c1176 := h 1175 (by decide)
  have h2 : Entails.eval a c1201 := h 1200 (by decide)
  have h3 : Entails.eval a c2056 := h 2055 (by decide)
  have h4 : Entails.eval a c821 := h 820 (by decide)
  have h5 : Entails.eval a c463 := h 462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7860 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7860 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7481, some c7473, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7860 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7860 : lratChecker f7860 p7860 = .success := by decide +kernel
theorem unsat7860 : Unsatisfiable (PosFin 65) f7860 := by
  apply lratCheckerSound f7860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7860
  · intro a ha; simp [p7860] at ha; subst a; trivial
  · exact checked7860
theorem derived7860 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7860 := by
  apply localUnsat_implies_entails f7860 [c7481, c7473] c7860 unsat7860 (by rfl) a
  have h0 : Entails.eval a c7481 := derived7481 a h
  have h1 : Entails.eval a c7473 := derived7473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7861 : DefaultClause 65 := directClause [(⟨9, by decide⟩, false), (⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7861 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7859, some c7860, some c1176, some c2280, some c2348, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7861 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7861 : lratChecker f7861 p7861 = .success := by decide +kernel
theorem unsat7861 : Unsatisfiable (PosFin 65) f7861 := by
  apply lratCheckerSound f7861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7861
  · intro a ha; simp [p7861] at ha; subst a; trivial
  · exact checked7861
theorem derived7861 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7861 := by
  apply localUnsat_implies_entails f7861 [c7859, c7860, c1176, c2280, c2348] c7861 unsat7861 (by rfl) a
  have h0 : Entails.eval a c7859 := derived7859 a h
  have h1 : Entails.eval a c7860 := derived7860 a h
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  have h3 : Entails.eval a c2280 := h 2279 (by decide)
  have h4 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7862 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7862 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c1199, some c1469, some c1506, some c820, some c821, some c845, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7862 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7862 : lratChecker f7862 p7862 = .success := by decide +kernel
theorem unsat7862 : Unsatisfiable (PosFin 65) f7862 := by
  apply lratCheckerSound f7862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7862
  · intro a ha; simp [p7862] at ha; subst a; trivial
  · exact checked7862
theorem derived7862 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7862 := by
  apply localUnsat_implies_entails f7862 [c1171, c1199, c1469, c1506, c820, c821, c845] c7862 unsat7862 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c1199 := h 1198 (by decide)
  have h2 : Entails.eval a c1469 := h 1468 (by decide)
  have h3 : Entails.eval a c1506 := h 1505 (by decide)
  have h4 : Entails.eval a c820 := h 819 (by decide)
  have h5 : Entails.eval a c821 := h 820 (by decide)
  have h6 : Entails.eval a c845 := h 844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7863 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7863 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7861, some c7855, some c7862, some c1176, some c2280, some c2348, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7863 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7863 : lratChecker f7863 p7863 = .success := by decide +kernel
theorem unsat7863 : Unsatisfiable (PosFin 65) f7863 := by
  apply lratCheckerSound f7863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7863
  · intro a ha; simp [p7863] at ha; subst a; trivial
  · exact checked7863
theorem derived7863 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7863 := by
  apply localUnsat_implies_entails f7863 [c7861, c7855, c7862, c1176, c2280, c2348] c7863 unsat7863 (by rfl) a
  have h0 : Entails.eval a c7861 := derived7861 a h
  have h1 : Entails.eval a c7855 := derived7855 a h
  have h2 : Entails.eval a c7862 := derived7862 a h
  have h3 : Entails.eval a c1176 := h 1175 (by decide)
  have h4 : Entails.eval a c2280 := h 2279 (by decide)
  have h5 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7864 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7864 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7857, some c7863, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7864 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7864 : lratChecker f7864 p7864 = .success := by decide +kernel
theorem unsat7864 : Unsatisfiable (PosFin 65) f7864 := by
  apply lratCheckerSound f7864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7864
  · intro a ha; simp [p7864] at ha; subst a; trivial
  · exact checked7864
theorem derived7864 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7864 := by
  apply localUnsat_implies_entails f7864 [c7849, c7857, c7863] c7864 unsat7864 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7857 := derived7857 a h
  have h2 : Entails.eval a c7863 := derived7863 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7865 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7865 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c1199, some c1035, some c1469, some c2063, some c1383, some c1506, some c652, some c468, some c591, some c845, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7865 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7865 : lratChecker f7865 p7865 = .success := by decide +kernel
theorem unsat7865 : Unsatisfiable (PosFin 65) f7865 := by
  apply lratCheckerSound f7865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7865
  · intro a ha; simp [p7865] at ha; subst a; trivial
  · exact checked7865
theorem derived7865 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7865 := by
  apply localUnsat_implies_entails f7865 [c1171, c1199, c1035, c1469, c2063, c1383, c1506, c652, c468, c591, c845] c7865 unsat7865 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c1199 := h 1198 (by decide)
  have h2 : Entails.eval a c1035 := h 1034 (by decide)
  have h3 : Entails.eval a c1469 := h 1468 (by decide)
  have h4 : Entails.eval a c2063 := h 2062 (by decide)
  have h5 : Entails.eval a c1383 := h 1382 (by decide)
  have h6 : Entails.eval a c1506 := h 1505 (by decide)
  have h7 : Entails.eval a c652 := h 651 (by decide)
  have h8 : Entails.eval a c468 := h 467 (by decide)
  have h9 : Entails.eval a c591 := h 590 (by decide)
  have h10 : Entails.eval a c845 := h 844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7866 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7866 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7853, some c7865, some c1176, some c1201, some c2280, some c1509, some c1381, some c825, some c652, some c534, some c549, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7866 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7866 : lratChecker f7866 p7866 = .success := by decide +kernel
theorem unsat7866 : Unsatisfiable (PosFin 65) f7866 := by
  apply lratCheckerSound f7866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7866
  · intro a ha; simp [p7866] at ha; subst a; trivial
  · exact checked7866
theorem derived7866 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7866 := by
  apply localUnsat_implies_entails f7866 [c7853, c7865, c1176, c1201, c2280, c1509, c1381, c825, c652, c534, c549] c7866 unsat7866 (by rfl) a
  have h0 : Entails.eval a c7853 := derived7853 a h
  have h1 : Entails.eval a c7865 := derived7865 a h
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  have h3 : Entails.eval a c1201 := h 1200 (by decide)
  have h4 : Entails.eval a c2280 := h 2279 (by decide)
  have h5 : Entails.eval a c1509 := h 1508 (by decide)
  have h6 : Entails.eval a c1381 := h 1380 (by decide)
  have h7 : Entails.eval a c825 := h 824 (by decide)
  have h8 : Entails.eval a c652 := h 651 (by decide)
  have h9 : Entails.eval a c534 := h 533 (by decide)
  have h10 : Entails.eval a c549 := h 548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7867 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7867 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7856, some c1176, some c2280, some c2348, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7867 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7867 : lratChecker f7867 p7867 = .success := by decide +kernel
theorem unsat7867 : Unsatisfiable (PosFin 65) f7867 := by
  apply lratCheckerSound f7867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7867
  · intro a ha; simp [p7867] at ha; subst a; trivial
  · exact checked7867
theorem derived7867 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7867 := by
  apply localUnsat_implies_entails f7867 [c7856, c1176, c2280, c2348] c7867 unsat7867 (by rfl) a
  have h0 : Entails.eval a c7856 := derived7856 a h
  have h1 : Entails.eval a c1176 := h 1175 (by decide)
  have h2 : Entails.eval a c2280 := h 2279 (by decide)
  have h3 : Entails.eval a c2348 := h 2347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7868 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7868 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7853, some c7867, some c7866, some c7854, some c1176, some c1201, some c1381, some c825, some c2505, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7868 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7868 : lratChecker f7868 p7868 = .success := by decide +kernel
theorem unsat7868 : Unsatisfiable (PosFin 65) f7868 := by
  apply lratCheckerSound f7868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7868
  · intro a ha; simp [p7868] at ha; subst a; trivial
  · exact checked7868
theorem derived7868 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7868 := by
  apply localUnsat_implies_entails f7868 [c7853, c7867, c7866, c7854, c1176, c1201, c1381, c825, c2505] c7868 unsat7868 (by rfl) a
  have h0 : Entails.eval a c7853 := derived7853 a h
  have h1 : Entails.eval a c7867 := derived7867 a h
  have h2 : Entails.eval a c7866 := derived7866 a h
  have h3 : Entails.eval a c7854 := derived7854 a h
  have h4 : Entails.eval a c1176 := h 1175 (by decide)
  have h5 : Entails.eval a c1201 := h 1200 (by decide)
  have h6 : Entails.eval a c1381 := h 1380 (by decide)
  have h7 : Entails.eval a c825 := h 824 (by decide)
  have h8 : Entails.eval a c2505 := h 2504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7869 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7869 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c1199, some c822, some c833, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7869 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7869 : lratChecker f7869 p7869 = .success := by decide +kernel
theorem unsat7869 : Unsatisfiable (PosFin 65) f7869 := by
  apply lratCheckerSound f7869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7869
  · intro a ha; simp [p7869] at ha; subst a; trivial
  · exact checked7869
theorem derived7869 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7869 := by
  apply localUnsat_implies_entails f7869 [c1171, c1199, c822, c833] c7869 unsat7869 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c1199 := h 1198 (by decide)
  have h2 : Entails.eval a c822 := h 821 (by decide)
  have h3 : Entails.eval a c833 := h 832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7870 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7870 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7853, some c7864, some c7868, some c7869, some c1176, some c1201, some c822, some c833, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7870 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7870 : lratChecker f7870 p7870 = .success := by decide +kernel
theorem unsat7870 : Unsatisfiable (PosFin 65) f7870 := by
  apply lratCheckerSound f7870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7870
  · intro a ha; simp [p7870] at ha; subst a; trivial
  · exact checked7870
theorem derived7870 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7870 := by
  apply localUnsat_implies_entails f7870 [c7849, c7853, c7864, c7868, c7869, c1176, c1201, c822, c833] c7870 unsat7870 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7853 := derived7853 a h
  have h2 : Entails.eval a c7864 := derived7864 a h
  have h3 : Entails.eval a c7868 := derived7868 a h
  have h4 : Entails.eval a c7869 := derived7869 a h
  have h5 : Entails.eval a c1176 := h 1175 (by decide)
  have h6 : Entails.eval a c1201 := h 1200 (by decide)
  have h7 : Entails.eval a c822 := h 821 (by decide)
  have h8 : Entails.eval a c833 := h 832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7871 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7871 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1169, some c1198, some c2289, some c1504, some c825, some c487, some c542, some c829, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7871 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7871 : lratChecker f7871 p7871 = .success := by decide +kernel
theorem unsat7871 : Unsatisfiable (PosFin 65) f7871 := by
  apply lratCheckerSound f7871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7871
  · intro a ha; simp [p7871] at ha; subst a; trivial
  · exact checked7871
theorem derived7871 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7871 := by
  apply localUnsat_implies_entails f7871 [c1169, c1198, c2289, c1504, c825, c487, c542, c829] c7871 unsat7871 (by rfl) a
  have h0 : Entails.eval a c1169 := h 1168 (by decide)
  have h1 : Entails.eval a c1198 := h 1197 (by decide)
  have h2 : Entails.eval a c2289 := h 2288 (by decide)
  have h3 : Entails.eval a c1504 := h 1503 (by decide)
  have h4 : Entails.eval a c825 := h 824 (by decide)
  have h5 : Entails.eval a c487 := h 486 (by decide)
  have h6 : Entails.eval a c542 := h 541 (by decide)
  have h7 : Entails.eval a c829 := h 828 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7872 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7872 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7853, some c7871, some c1176, some c1201, some c2280, some c1509, some c1472, some c825, some c487, some c542, some c857, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7872 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7872 : lratChecker f7872 p7872 = .success := by decide +kernel
theorem unsat7872 : Unsatisfiable (PosFin 65) f7872 := by
  apply lratCheckerSound f7872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7872
  · intro a ha; simp [p7872] at ha; subst a; trivial
  · exact checked7872
theorem derived7872 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7872 := by
  apply localUnsat_implies_entails f7872 [c7853, c7871, c1176, c1201, c2280, c1509, c1472, c825, c487, c542, c857] c7872 unsat7872 (by rfl) a
  have h0 : Entails.eval a c7853 := derived7853 a h
  have h1 : Entails.eval a c7871 := derived7871 a h
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  have h3 : Entails.eval a c1201 := h 1200 (by decide)
  have h4 : Entails.eval a c2280 := h 2279 (by decide)
  have h5 : Entails.eval a c1509 := h 1508 (by decide)
  have h6 : Entails.eval a c1472 := h 1471 (by decide)
  have h7 : Entails.eval a c825 := h 824 (by decide)
  have h8 : Entails.eval a c487 := h 486 (by decide)
  have h9 : Entails.eval a c542 := h 541 (by decide)
  have h10 : Entails.eval a c857 := h 856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7873 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7873 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c820, some c827, some c2285, some c2351, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7873 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7873 : lratChecker f7873 p7873 = .success := by decide +kernel
theorem unsat7873 : Unsatisfiable (PosFin 65) f7873 := by
  apply lratCheckerSound f7873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7873
  · intro a ha; simp [p7873] at ha; subst a; trivial
  · exact checked7873
theorem derived7873 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7873 := by
  apply localUnsat_implies_entails f7873 [c820, c827, c2285, c2351] c7873 unsat7873 (by rfl) a
  have h0 : Entails.eval a c820 := h 819 (by decide)
  have h1 : Entails.eval a c827 := h 826 (by decide)
  have h2 : Entails.eval a c2285 := h 2284 (by decide)
  have h3 : Entails.eval a c2351 := h 2350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7874 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7874 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1200, some c1210, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7874 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7874 : lratChecker f7874 p7874 = .success := by decide +kernel
theorem unsat7874 : Unsatisfiable (PosFin 65) f7874 := by
  apply lratCheckerSound f7874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7874
  · intro a ha; simp [p7874] at ha; subst a; trivial
  · exact checked7874
theorem derived7874 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7874 := by
  apply localUnsat_implies_entails f7874 [c1200, c1210] c7874 unsat7874 (by rfl) a
  have h0 : Entails.eval a c1200 := h 1199 (by decide)
  have h1 : Entails.eval a c1210 := h 1209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7875 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7875 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c820, some c821, some c7873, some c1539, some c1470, some c2285, some c2274, some c2065, some c430, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7875 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7875 : lratChecker f7875 p7875 = .success := by decide +kernel
theorem unsat7875 : Unsatisfiable (PosFin 65) f7875 := by
  apply lratCheckerSound f7875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7875
  · intro a ha; simp [p7875] at ha; subst a; trivial
  · exact checked7875
theorem derived7875 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7875 := by
  apply localUnsat_implies_entails f7875 [c820, c821, c7873, c1539, c1470, c2285, c2274, c2065, c430] c7875 unsat7875 (by rfl) a
  have h0 : Entails.eval a c820 := h 819 (by decide)
  have h1 : Entails.eval a c821 := h 820 (by decide)
  have h2 : Entails.eval a c7873 := derived7873 a h
  have h3 : Entails.eval a c1539 := h 1538 (by decide)
  have h4 : Entails.eval a c1470 := h 1469 (by decide)
  have h5 : Entails.eval a c2285 := h 2284 (by decide)
  have h6 : Entails.eval a c2274 := h 2273 (by decide)
  have h7 : Entails.eval a c2065 := h 2064 (by decide)
  have h8 : Entails.eval a c430 := h 429 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7876 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7876 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7874, some c7875, some c1190, some c1170, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7876 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7876 : lratChecker f7876 p7876 = .success := by decide +kernel
theorem unsat7876 : Unsatisfiable (PosFin 65) f7876 := by
  apply lratCheckerSound f7876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7876
  · intro a ha; simp [p7876] at ha; subst a; trivial
  · exact checked7876
theorem derived7876 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7876 := by
  apply localUnsat_implies_entails f7876 [c7874, c7875, c1190, c1170] c7876 unsat7876 (by rfl) a
  have h0 : Entails.eval a c7874 := derived7874 a h
  have h1 : Entails.eval a c7875 := derived7875 a h
  have h2 : Entails.eval a c1190 := h 1189 (by decide)
  have h3 : Entails.eval a c1170 := h 1169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7877 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7877 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7853, some c7872, some c7876, some c1176, some c1201, some c2280, some c1509, some c833, some c487, some c542, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7877 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7877 : lratChecker f7877 p7877 = .success := by decide +kernel
theorem unsat7877 : Unsatisfiable (PosFin 65) f7877 := by
  apply lratCheckerSound f7877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7877
  · intro a ha; simp [p7877] at ha; subst a; trivial
  · exact checked7877
theorem derived7877 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7877 := by
  apply localUnsat_implies_entails f7877 [c7853, c7872, c7876, c1176, c1201, c2280, c1509, c833, c487, c542] c7877 unsat7877 (by rfl) a
  have h0 : Entails.eval a c7853 := derived7853 a h
  have h1 : Entails.eval a c7872 := derived7872 a h
  have h2 : Entails.eval a c7876 := derived7876 a h
  have h3 : Entails.eval a c1176 := h 1175 (by decide)
  have h4 : Entails.eval a c1201 := h 1200 (by decide)
  have h5 : Entails.eval a c2280 := h 2279 (by decide)
  have h6 : Entails.eval a c1509 := h 1508 (by decide)
  have h7 : Entails.eval a c833 := h 832 (by decide)
  have h8 : Entails.eval a c487 := h 486 (by decide)
  have h9 : Entails.eval a c542 := h 541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7878 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7878 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1169, some c1198, some c2289, some c1504, some c825, some c820, some c534, some c826, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7878 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7878 : lratChecker f7878 p7878 = .success := by decide +kernel
theorem unsat7878 : Unsatisfiable (PosFin 65) f7878 := by
  apply lratCheckerSound f7878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7878
  · intro a ha; simp [p7878] at ha; subst a; trivial
  · exact checked7878
theorem derived7878 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7878 := by
  apply localUnsat_implies_entails f7878 [c1169, c1198, c2289, c1504, c825, c820, c534, c826] c7878 unsat7878 (by rfl) a
  have h0 : Entails.eval a c1169 := h 1168 (by decide)
  have h1 : Entails.eval a c1198 := h 1197 (by decide)
  have h2 : Entails.eval a c2289 := h 2288 (by decide)
  have h3 : Entails.eval a c1504 := h 1503 (by decide)
  have h4 : Entails.eval a c825 := h 824 (by decide)
  have h5 : Entails.eval a c820 := h 819 (by decide)
  have h6 : Entails.eval a c534 := h 533 (by decide)
  have h7 : Entails.eval a c826 := h 825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7879 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7879 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7853, some c7878, some c1176, some c1201, some c1509, some c1472, some c825, some c822, some c857, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7879 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7879 : lratChecker f7879 p7879 = .success := by decide +kernel
theorem unsat7879 : Unsatisfiable (PosFin 65) f7879 := by
  apply lratCheckerSound f7879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7879
  · intro a ha; simp [p7879] at ha; subst a; trivial
  · exact checked7879
theorem derived7879 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7879 := by
  apply localUnsat_implies_entails f7879 [c7853, c7878, c1176, c1201, c1509, c1472, c825, c822, c857] c7879 unsat7879 (by rfl) a
  have h0 : Entails.eval a c7853 := derived7853 a h
  have h1 : Entails.eval a c7878 := derived7878 a h
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  have h3 : Entails.eval a c1201 := h 1200 (by decide)
  have h4 : Entails.eval a c1509 := h 1508 (by decide)
  have h5 : Entails.eval a c1472 := h 1471 (by decide)
  have h6 : Entails.eval a c825 := h 824 (by decide)
  have h7 : Entails.eval a c822 := h 821 (by decide)
  have h8 : Entails.eval a c857 := h 856 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7880 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7880 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c822, some c833, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7880 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7880 : lratChecker f7880 p7880 = .success := by decide +kernel
theorem unsat7880 : Unsatisfiable (PosFin 65) f7880 := by
  apply lratCheckerSound f7880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7880
  · intro a ha; simp [p7880] at ha; subst a; trivial
  · exact checked7880
theorem derived7880 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7880 := by
  apply localUnsat_implies_entails f7880 [c822, c833] c7880 unsat7880 (by rfl) a
  have h0 : Entails.eval a c822 := h 821 (by decide)
  have h1 : Entails.eval a c833 := h 832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived7880

end CochromaticTwenty.Certificates.FixedCore1
