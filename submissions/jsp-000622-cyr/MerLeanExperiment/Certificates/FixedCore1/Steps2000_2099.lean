import MerLeanExperiment.Certificates.FixedCore1.Steps1900_1999

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7881 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7881 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7874, some c7880, some c1190, some c1170, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7881 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7881 : lratChecker f7881 p7881 = .success := by decide +kernel
theorem unsat7881 : Unsatisfiable (PosFin 65) f7881 := by
  apply lratCheckerSound f7881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7881
  · intro a ha; simp [p7881] at ha; subst a; trivial
  · exact checked7881
theorem derived7881 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7881 := by
  apply localUnsat_implies_entails f7881 [c7874, c7880, c1190, c1170] c7881 unsat7881 (by rfl) a
  have h0 : Entails.eval a c7874 := derived7874 a h
  have h1 : Entails.eval a c7880 := derived7880 a h
  have h2 : Entails.eval a c1190 := h 1189 (by decide)
  have h3 : Entails.eval a c1170 := h 1169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7882 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7882 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7853, some c7870, some c7877, some c7879, some c7881, some c1176, some c1201, some c822, some c833, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7882 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7882 : lratChecker f7882 p7882 = .success := by decide +kernel
theorem unsat7882 : Unsatisfiable (PosFin 65) f7882 := by
  apply lratCheckerSound f7882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7882
  · intro a ha; simp [p7882] at ha; subst a; trivial
  · exact checked7882
theorem derived7882 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7882 := by
  apply localUnsat_implies_entails f7882 [c7849, c7853, c7870, c7877, c7879, c7881, c1176, c1201, c822, c833] c7882 unsat7882 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7853 := derived7853 a h
  have h2 : Entails.eval a c7870 := derived7870 a h
  have h3 : Entails.eval a c7877 := derived7877 a h
  have h4 : Entails.eval a c7879 := derived7879 a h
  have h5 : Entails.eval a c7881 := derived7881 a h
  have h6 : Entails.eval a c1176 := h 1175 (by decide)
  have h7 : Entails.eval a c1201 := h 1200 (by decide)
  have h8 : Entails.eval a c822 := h 821 (by decide)
  have h9 : Entails.eval a c833 := h 832 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7883 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7883 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2280, some c1509, some c1022, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7883 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7883 : lratChecker f7883 p7883 = .success := by decide +kernel
theorem unsat7883 : Unsatisfiable (PosFin 65) f7883 := by
  apply lratCheckerSound f7883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7883
  · intro a ha; simp [p7883] at ha; subst a; trivial
  · exact checked7883
theorem derived7883 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7883 := by
  apply localUnsat_implies_entails f7883 [c2280, c1509, c1022] c7883 unsat7883 (by rfl) a
  have h0 : Entails.eval a c2280 := h 2279 (by decide)
  have h1 : Entails.eval a c1509 := h 1508 (by decide)
  have h2 : Entails.eval a c1022 := h 1021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7884 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7884 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7882, some c7883, some c7570, some c2291, some c1515, some c521, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7884 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7884 : lratChecker f7884 p7884 = .success := by decide +kernel
theorem unsat7884 : Unsatisfiable (PosFin 65) f7884 := by
  apply lratCheckerSound f7884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7884
  · intro a ha; simp [p7884] at ha; subst a; trivial
  · exact checked7884
theorem derived7884 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7884 := by
  apply localUnsat_implies_entails f7884 [c7849, c7882, c7883, c7570, c2291, c1515, c521] c7884 unsat7884 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7882 := derived7882 a h
  have h2 : Entails.eval a c7883 := derived7883 a h
  have h3 : Entails.eval a c7570 := derived7570 a h
  have h4 : Entails.eval a c2291 := h 2290 (by decide)
  have h5 : Entails.eval a c1515 := h 1514 (by decide)
  have h6 : Entails.eval a c521 := h 520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7885 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7885 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1469, some c1506, some c2674, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7885 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7885 : lratChecker f7885 p7885 = .success := by decide +kernel
theorem unsat7885 : Unsatisfiable (PosFin 65) f7885 := by
  apply lratCheckerSound f7885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7885
  · intro a ha; simp [p7885] at ha; subst a; trivial
  · exact checked7885
theorem derived7885 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7885 := by
  apply localUnsat_implies_entails f7885 [c1469, c1506, c2674] c7885 unsat7885 (by rfl) a
  have h0 : Entails.eval a c1469 := h 1468 (by decide)
  have h1 : Entails.eval a c1506 := h 1505 (by decide)
  have h2 : Entails.eval a c2674 := h 2673 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7886 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7886 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1475, some c1515, some c2678, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7886 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7886 : lratChecker f7886 p7886 = .success := by decide +kernel
theorem unsat7886 : Unsatisfiable (PosFin 65) f7886 := by
  apply lratCheckerSound f7886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7886
  · intro a ha; simp [p7886] at ha; subst a; trivial
  · exact checked7886
theorem derived7886 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7886 := by
  apply localUnsat_implies_entails f7886 [c1475, c1515, c2678] c7886 unsat7886 (by rfl) a
  have h0 : Entails.eval a c1475 := h 1474 (by decide)
  have h1 : Entails.eval a c1515 := h 1514 (by decide)
  have h2 : Entails.eval a c2678 := h 2677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7887 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7887 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7884, some c7735, some c7886, some c1470, some c1507, some c2675, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7887 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7887 : lratChecker f7887 p7887 = .success := by decide +kernel
theorem unsat7887 : Unsatisfiable (PosFin 65) f7887 := by
  apply lratCheckerSound f7887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7887
  · intro a ha; simp [p7887] at ha; subst a; trivial
  · exact checked7887
theorem derived7887 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7887 := by
  apply localUnsat_implies_entails f7887 [c7884, c7735, c7886, c1470, c1507, c2675] c7887 unsat7887 (by rfl) a
  have h0 : Entails.eval a c7884 := derived7884 a h
  have h1 : Entails.eval a c7735 := derived7735 a h
  have h2 : Entails.eval a c7886 := derived7886 a h
  have h3 : Entails.eval a c1470 := h 1469 (by decide)
  have h4 : Entails.eval a c1507 := h 1506 (by decide)
  have h5 : Entails.eval a c2675 := h 2674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7888 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7888 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1171, some c1199, some c828, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7888 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7888 : lratChecker f7888 p7888 = .success := by decide +kernel
theorem unsat7888 : Unsatisfiable (PosFin 65) f7888 := by
  apply lratCheckerSound f7888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7888
  · intro a ha; simp [p7888] at ha; subst a; trivial
  · exact checked7888
theorem derived7888 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7888 := by
  apply localUnsat_implies_entails f7888 [c1171, c1199, c828] c7888 unsat7888 (by rfl) a
  have h0 : Entails.eval a c1171 := h 1170 (by decide)
  have h1 : Entails.eval a c1199 := h 1198 (by decide)
  have h2 : Entails.eval a c828 := h 827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7889 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7889 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c832, some c827, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7889 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7889 : lratChecker f7889 p7889 = .success := by decide +kernel
theorem unsat7889 : Unsatisfiable (PosFin 65) f7889 := by
  apply lratCheckerSound f7889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7889
  · intro a ha; simp [p7889] at ha; subst a; trivial
  · exact checked7889
theorem derived7889 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7889 := by
  apply localUnsat_implies_entails f7889 [c832, c827] c7889 unsat7889 (by rfl) a
  have h0 : Entails.eval a c832 := h 831 (by decide)
  have h1 : Entails.eval a c827 := h 826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7890 : DefaultClause 65 := directClause [(⟨30, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7890 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7888, some c7874, some c7889, some c1192, some c1187, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7890 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7890 : lratChecker f7890 p7890 = .success := by decide +kernel
theorem unsat7890 : Unsatisfiable (PosFin 65) f7890 := by
  apply lratCheckerSound f7890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7890
  · intro a ha; simp [p7890] at ha; subst a; trivial
  · exact checked7890
theorem derived7890 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7890 := by
  apply localUnsat_implies_entails f7890 [c7888, c7874, c7889, c1192, c1187] c7890 unsat7890 (by rfl) a
  have h0 : Entails.eval a c7888 := derived7888 a h
  have h1 : Entails.eval a c7874 := derived7874 a h
  have h2 : Entails.eval a c7889 := derived7889 a h
  have h3 : Entails.eval a c1192 := h 1191 (by decide)
  have h4 : Entails.eval a c1187 := h 1186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7891 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7891 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7890, some c1177, some c1202, some c2289, some c832, some c834, some c511, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7891 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7891 : lratChecker f7891 p7891 = .success := by decide +kernel
theorem unsat7891 : Unsatisfiable (PosFin 65) f7891 := by
  apply lratCheckerSound f7891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7891
  · intro a ha; simp [p7891] at ha; subst a; trivial
  · exact checked7891
theorem derived7891 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7891 := by
  apply localUnsat_implies_entails f7891 [c7890, c1177, c1202, c2289, c832, c834, c511] c7891 unsat7891 (by rfl) a
  have h0 : Entails.eval a c7890 := derived7890 a h
  have h1 : Entails.eval a c1177 := h 1176 (by decide)
  have h2 : Entails.eval a c1202 := h 1201 (by decide)
  have h3 : Entails.eval a c2289 := h 2288 (by decide)
  have h4 : Entails.eval a c832 := h 831 (by decide)
  have h5 : Entails.eval a c834 := h 833 (by decide)
  have h6 : Entails.eval a c511 := h 510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7892 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7892 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7672, some c7570, some c2289, some c1003, some c1386, some c2652, some c7574, some c660, some c1504, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7892 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7892 : lratChecker f7892 p7892 = .success := by decide +kernel
theorem unsat7892 : Unsatisfiable (PosFin 65) f7892 := by
  apply lratCheckerSound f7892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7892
  · intro a ha; simp [p7892] at ha; subst a; trivial
  · exact checked7892
theorem derived7892 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7892 := by
  apply localUnsat_implies_entails f7892 [c7672, c7570, c2289, c1003, c1386, c2652, c7574, c660, c1504] c7892 unsat7892 (by rfl) a
  have h0 : Entails.eval a c7672 := derived7672 a h
  have h1 : Entails.eval a c7570 := derived7570 a h
  have h2 : Entails.eval a c2289 := h 2288 (by decide)
  have h3 : Entails.eval a c1003 := h 1002 (by decide)
  have h4 : Entails.eval a c1386 := h 1385 (by decide)
  have h5 : Entails.eval a c2652 := h 2651 (by decide)
  have h6 : Entails.eval a c7574 := derived7574 a h
  have h7 : Entails.eval a c660 := h 659 (by decide)
  have h8 : Entails.eval a c1504 := h 1503 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7893 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7893 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1511, some c2288, some c1024, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7893 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7893 : lratChecker f7893 p7893 = .success := by decide +kernel
theorem unsat7893 : Unsatisfiable (PosFin 65) f7893 := by
  apply lratCheckerSound f7893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7893
  · intro a ha; simp [p7893] at ha; subst a; trivial
  · exact checked7893
theorem derived7893 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7893 := by
  apply localUnsat_implies_entails f7893 [c1511, c2288, c1024] c7893 unsat7893 (by rfl) a
  have h0 : Entails.eval a c1511 := h 1510 (by decide)
  have h1 : Entails.eval a c2288 := h 2287 (by decide)
  have h2 : Entails.eval a c1024 := h 1023 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7894 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7894 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7891, some c7570, some c7672, some c7893, some c1525, some c1476, some c1236, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7894 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7894 : lratChecker f7894 p7894 = .success := by decide +kernel
theorem unsat7894 : Unsatisfiable (PosFin 65) f7894 := by
  apply lratCheckerSound f7894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7894
  · intro a ha; simp [p7894] at ha; subst a; trivial
  · exact checked7894
theorem derived7894 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7894 := by
  apply localUnsat_implies_entails f7894 [c7891, c7570, c7672, c7893, c1525, c1476, c1236] c7894 unsat7894 (by rfl) a
  have h0 : Entails.eval a c7891 := derived7891 a h
  have h1 : Entails.eval a c7570 := derived7570 a h
  have h2 : Entails.eval a c7672 := derived7672 a h
  have h3 : Entails.eval a c7893 := derived7893 a h
  have h4 : Entails.eval a c1525 := h 1524 (by decide)
  have h5 : Entails.eval a c1476 := h 1475 (by decide)
  have h6 : Entails.eval a c1236 := h 1235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7895 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7895 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1188, some c1211, some c828, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7895 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7895 : lratChecker f7895 p7895 = .success := by decide +kernel
theorem unsat7895 : Unsatisfiable (PosFin 65) f7895 := by
  apply lratCheckerSound f7895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7895
  · intro a ha; simp [p7895] at ha; subst a; trivial
  · exact checked7895
theorem derived7895 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7895 := by
  apply localUnsat_implies_entails f7895 [c1188, c1211, c828] c7895 unsat7895 (by rfl) a
  have h0 : Entails.eval a c1188 := h 1187 (by decide)
  have h1 : Entails.eval a c1211 := h 1210 (by decide)
  have h2 : Entails.eval a c828 := h 827 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7896 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7896 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1465, some c1501, some c2279, some c837, some c554, some c531, some c548, some c1167, some c495, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7896 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7896 : lratChecker f7896 p7896 = .success := by decide +kernel
theorem unsat7896 : Unsatisfiable (PosFin 65) f7896 := by
  apply lratCheckerSound f7896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7896
  · intro a ha; simp [p7896] at ha; subst a; trivial
  · exact checked7896
theorem derived7896 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7896 := by
  apply localUnsat_implies_entails f7896 [c1465, c1501, c2279, c837, c554, c531, c548, c1167, c495] c7896 unsat7896 (by rfl) a
  have h0 : Entails.eval a c1465 := h 1464 (by decide)
  have h1 : Entails.eval a c1501 := h 1500 (by decide)
  have h2 : Entails.eval a c2279 := h 2278 (by decide)
  have h3 : Entails.eval a c837 := h 836 (by decide)
  have h4 : Entails.eval a c554 := h 553 (by decide)
  have h5 : Entails.eval a c531 := h 530 (by decide)
  have h6 : Entails.eval a c548 := h 547 (by decide)
  have h7 : Entails.eval a c1167 := h 1166 (by decide)
  have h8 : Entails.eval a c495 := h 494 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7897 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨30, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7897 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c835, some c823, some c1467, some c1503, some c856, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7897 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7897 : lratChecker f7897 p7897 = .success := by decide +kernel
theorem unsat7897 : Unsatisfiable (PosFin 65) f7897 := by
  apply lratCheckerSound f7897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7897
  · intro a ha; simp [p7897] at ha; subst a; trivial
  · exact checked7897
theorem derived7897 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7897 := by
  apply localUnsat_implies_entails f7897 [c835, c823, c1467, c1503, c856] c7897 unsat7897 (by rfl) a
  have h0 : Entails.eval a c835 := h 834 (by decide)
  have h1 : Entails.eval a c823 := h 822 (by decide)
  have h2 : Entails.eval a c1467 := h 1466 (by decide)
  have h3 : Entails.eval a c1503 := h 1502 (by decide)
  have h4 : Entails.eval a c856 := h 855 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7898 : DefaultClause 65 := directClause [(⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7898 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1213, some c1197, some c1207, some c1203, some c1205, some c1209, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7898 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7898 : lratChecker f7898 p7898 = .success := by decide +kernel
theorem unsat7898 : Unsatisfiable (PosFin 65) f7898 := by
  apply lratCheckerSound f7898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7898
  · intro a ha; simp [p7898] at ha; subst a; trivial
  · exact checked7898
theorem derived7898 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7898 := by
  apply localUnsat_implies_entails f7898 [c1213, c1197, c1207, c1203, c1205, c1209] c7898 unsat7898 (by rfl) a
  have h0 : Entails.eval a c1213 := h 1212 (by decide)
  have h1 : Entails.eval a c1197 := h 1196 (by decide)
  have h2 : Entails.eval a c1207 := h 1206 (by decide)
  have h3 : Entails.eval a c1203 := h 1202 (by decide)
  have h4 : Entails.eval a c1205 := h 1204 (by decide)
  have h5 : Entails.eval a c1209 := h 1208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7899 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7899 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7895, some c7898, some c1192, some c1168, some c1182, some c1179, some c1181, some c1186, some c2296, some c464, some c655, some c528, some c2172, some c2050, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7899 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7899 : lratChecker f7899 p7899 = .success := by decide +kernel
theorem unsat7899 : Unsatisfiable (PosFin 65) f7899 := by
  apply lratCheckerSound f7899 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7899
  · intro a ha; simp [p7899] at ha; subst a; trivial
  · exact checked7899
theorem derived7899 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7899 := by
  apply localUnsat_implies_entails f7899 [c7895, c7898, c1192, c1168, c1182, c1179, c1181, c1186, c2296, c464, c655, c528, c2172, c2050] c7899 unsat7899 (by rfl) a
  have h0 : Entails.eval a c7895 := derived7895 a h
  have h1 : Entails.eval a c7898 := derived7898 a h
  have h2 : Entails.eval a c1192 := h 1191 (by decide)
  have h3 : Entails.eval a c1168 := h 1167 (by decide)
  have h4 : Entails.eval a c1182 := h 1181 (by decide)
  have h5 : Entails.eval a c1179 := h 1178 (by decide)
  have h6 : Entails.eval a c1181 := h 1180 (by decide)
  have h7 : Entails.eval a c1186 := h 1185 (by decide)
  have h8 : Entails.eval a c2296 := h 2295 (by decide)
  have h9 : Entails.eval a c464 := h 463 (by decide)
  have h10 : Entails.eval a c655 := h 654 (by decide)
  have h11 : Entails.eval a c528 := h 527 (by decide)
  have h12 : Entails.eval a c2172 := h 2171 (by decide)
  have h13 : Entails.eval a c2050 := h 2049 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7900 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7900 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7894, some c7895, some c7896, some c7898, some c7899, some c7889, some c7897, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7900 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7900 : lratChecker f7900 p7900 = .success := by decide +kernel
theorem unsat7900 : Unsatisfiable (PosFin 65) f7900 := by
  apply lratCheckerSound f7900 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7900
  · intro a ha; simp [p7900] at ha; subst a; trivial
  · exact checked7900
theorem derived7900 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7900 := by
  apply localUnsat_implies_entails f7900 [c7894, c7895, c7896, c7898, c7899, c7889, c7897] c7900 unsat7900 (by rfl) a
  have h0 : Entails.eval a c7894 := derived7894 a h
  have h1 : Entails.eval a c7895 := derived7895 a h
  have h2 : Entails.eval a c7896 := derived7896 a h
  have h3 : Entails.eval a c7898 := derived7898 a h
  have h4 : Entails.eval a c7899 := derived7899 a h
  have h5 : Entails.eval a c7889 := derived7889 a h
  have h6 : Entails.eval a c7897 := derived7897 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7901 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7901 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1490, some c1160, some c2541, some c2655, some c663, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7901 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7901 : lratChecker f7901 p7901 = .success := by decide +kernel
theorem unsat7901 : Unsatisfiable (PosFin 65) f7901 := by
  apply lratCheckerSound f7901 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7901
  · intro a ha; simp [p7901] at ha; subst a; trivial
  · exact checked7901
theorem derived7901 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7901 := by
  apply localUnsat_implies_entails f7901 [c1490, c1160, c2541, c2655, c663] c7901 unsat7901 (by rfl) a
  have h0 : Entails.eval a c1490 := h 1489 (by decide)
  have h1 : Entails.eval a c1160 := h 1159 (by decide)
  have h2 : Entails.eval a c2541 := h 2540 (by decide)
  have h3 : Entails.eval a c2655 := h 2654 (by decide)
  have h4 : Entails.eval a c663 := h 662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7902 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7902 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1465, some c1501, some c2279, some c1015, some c1223, some c530, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7902 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7902 : lratChecker f7902 p7902 = .success := by decide +kernel
theorem unsat7902 : Unsatisfiable (PosFin 65) f7902 := by
  apply lratCheckerSound f7902 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7902
  · intro a ha; simp [p7902] at ha; subst a; trivial
  · exact checked7902
theorem derived7902 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7902 := by
  apply localUnsat_implies_entails f7902 [c1465, c1501, c2279, c1015, c1223, c530] c7902 unsat7902 (by rfl) a
  have h0 : Entails.eval a c1465 := h 1464 (by decide)
  have h1 : Entails.eval a c1501 := h 1500 (by decide)
  have h2 : Entails.eval a c2279 := h 2278 (by decide)
  have h3 : Entails.eval a c1015 := h 1014 (by decide)
  have h4 : Entails.eval a c1223 := h 1222 (by decide)
  have h5 : Entails.eval a c530 := h 529 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7903 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7903 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1023, some c537, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7903 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7903 : lratChecker f7903 p7903 = .success := by decide +kernel
theorem unsat7903 : Unsatisfiable (PosFin 65) f7903 := by
  apply lratCheckerSound f7903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7903
  · intro a ha; simp [p7903] at ha; subst a; trivial
  · exact checked7903
theorem derived7903 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7903 := by
  apply localUnsat_implies_entails f7903 [c1023, c537] c7903 unsat7903 (by rfl) a
  have h0 : Entails.eval a c1023 := h 1022 (by decide)
  have h1 : Entails.eval a c537 := h 536 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7904 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7904 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7903, some c2310, some c2297, some c2301, some c2296, some c2233, some c2307, some c7506, some c674, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7904 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7904 : lratChecker f7904 p7904 = .success := by decide +kernel
theorem unsat7904 : Unsatisfiable (PosFin 65) f7904 := by
  apply lratCheckerSound f7904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7904
  · intro a ha; simp [p7904] at ha; subst a; trivial
  · exact checked7904
theorem derived7904 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7904 := by
  apply localUnsat_implies_entails f7904 [c7903, c2310, c2297, c2301, c2296, c2233, c2307, c7506, c674] c7904 unsat7904 (by rfl) a
  have h0 : Entails.eval a c7903 := derived7903 a h
  have h1 : Entails.eval a c2310 := h 2309 (by decide)
  have h2 : Entails.eval a c2297 := h 2296 (by decide)
  have h3 : Entails.eval a c2301 := h 2300 (by decide)
  have h4 : Entails.eval a c2296 := h 2295 (by decide)
  have h5 : Entails.eval a c2233 := h 2232 (by decide)
  have h6 : Entails.eval a c2307 := h 2306 (by decide)
  have h7 : Entails.eval a c7506 := derived7506 a h
  have h8 : Entails.eval a c674 := h 673 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7905 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7905 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7894, some c7900, some c7901, some c7902, some c7904, some c1510, some c1521, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7905 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7905 : lratChecker f7905 p7905 = .success := by decide +kernel
theorem unsat7905 : Unsatisfiable (PosFin 65) f7905 := by
  apply lratCheckerSound f7905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7905
  · intro a ha; simp [p7905] at ha; subst a; trivial
  · exact checked7905
theorem derived7905 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7905 := by
  apply localUnsat_implies_entails f7905 [c7894, c7900, c7901, c7902, c7904, c1510, c1521] c7905 unsat7905 (by rfl) a
  have h0 : Entails.eval a c7894 := derived7894 a h
  have h1 : Entails.eval a c7900 := derived7900 a h
  have h2 : Entails.eval a c7901 := derived7901 a h
  have h3 : Entails.eval a c7902 := derived7902 a h
  have h4 : Entails.eval a c7904 := derived7904 a h
  have h5 : Entails.eval a c1510 := h 1509 (by decide)
  have h6 : Entails.eval a c1521 := h 1520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7906 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7906 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c835, some c832, some c826, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7906 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7906 : lratChecker f7906 p7906 = .success := by decide +kernel
theorem unsat7906 : Unsatisfiable (PosFin 65) f7906 := by
  apply lratCheckerSound f7906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7906
  · intro a ha; simp [p7906] at ha; subst a; trivial
  · exact checked7906
theorem derived7906 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7906 := by
  apply localUnsat_implies_entails f7906 [c835, c832, c826] c7906 unsat7906 (by rfl) a
  have h0 : Entails.eval a c835 := h 834 (by decide)
  have h1 : Entails.eval a c832 := h 831 (by decide)
  have h2 : Entails.eval a c826 := h 825 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7907 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨30, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7907 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c943, some c1097, some c1758, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7907 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7907 : lratChecker f7907 p7907 = .success := by decide +kernel
theorem unsat7907 : Unsatisfiable (PosFin 65) f7907 := by
  apply lratCheckerSound f7907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7907
  · intro a ha; simp [p7907] at ha; subst a; trivial
  · exact checked7907
theorem derived7907 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7907 := by
  apply localUnsat_implies_entails f7907 [c943, c1097, c1758] c7907 unsat7907 (by rfl) a
  have h0 : Entails.eval a c943 := h 942 (by decide)
  have h1 : Entails.eval a c1097 := h 1096 (by decide)
  have h2 : Entails.eval a c1758 := h 1757 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7908 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7908 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7907, some c7906, some c957, some c1042, some c1706, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7908 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7908 : lratChecker f7908 p7908 = .success := by decide +kernel
theorem unsat7908 : Unsatisfiable (PosFin 65) f7908 := by
  apply lratCheckerSound f7908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7908
  · intro a ha; simp [p7908] at ha; subst a; trivial
  · exact checked7908
theorem derived7908 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7908 := by
  apply localUnsat_implies_entails f7908 [c7907, c7906, c957, c1042, c1706] c7908 unsat7908 (by rfl) a
  have h0 : Entails.eval a c7907 := derived7907 a h
  have h1 : Entails.eval a c7906 := derived7906 a h
  have h2 : Entails.eval a c957 := h 956 (by decide)
  have h3 : Entails.eval a c1042 := h 1041 (by decide)
  have h4 : Entails.eval a c1706 := h 1705 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7909 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7909 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c518, some c527, some c1474, some c847, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7909 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7909 : lratChecker f7909 p7909 = .success := by decide +kernel
theorem unsat7909 : Unsatisfiable (PosFin 65) f7909 := by
  apply lratCheckerSound f7909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7909
  · intro a ha; simp [p7909] at ha; subst a; trivial
  · exact checked7909
theorem derived7909 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7909 := by
  apply localUnsat_implies_entails f7909 [c518, c527, c1474, c847] c7909 unsat7909 (by rfl) a
  have h0 : Entails.eval a c518 := h 517 (by decide)
  have h1 : Entails.eval a c527 := h 526 (by decide)
  have h2 : Entails.eval a c1474 := h 1473 (by decide)
  have h3 : Entails.eval a c847 := h 846 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7910 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7910 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1471, some c640, some c2209, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7910 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7910 : lratChecker f7910 p7910 = .success := by decide +kernel
theorem unsat7910 : Unsatisfiable (PosFin 65) f7910 := by
  apply lratCheckerSound f7910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7910
  · intro a ha; simp [p7910] at ha; subst a; trivial
  · exact checked7910
theorem derived7910 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7910 := by
  apply localUnsat_implies_entails f7910 [c1471, c640, c2209] c7910 unsat7910 (by rfl) a
  have h0 : Entails.eval a c1471 := h 1470 (by decide)
  have h1 : Entails.eval a c640 := h 639 (by decide)
  have h2 : Entails.eval a c2209 := h 2208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7911 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7911 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7885, some c7908, some c7909, some c7910, some c1103, some c2605, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7911 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7911 : lratChecker f7911 p7911 = .success := by decide +kernel
theorem unsat7911 : Unsatisfiable (PosFin 65) f7911 := by
  apply lratCheckerSound f7911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7911
  · intro a ha; simp [p7911] at ha; subst a; trivial
  · exact checked7911
theorem derived7911 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7911 := by
  apply localUnsat_implies_entails f7911 [c7885, c7908, c7909, c7910, c1103, c2605] c7911 unsat7911 (by rfl) a
  have h0 : Entails.eval a c7885 := derived7885 a h
  have h1 : Entails.eval a c7908 := derived7908 a h
  have h2 : Entails.eval a c7909 := derived7909 a h
  have h3 : Entails.eval a c7910 := derived7910 a h
  have h4 : Entails.eval a c1103 := h 1102 (by decide)
  have h5 : Entails.eval a c2605 := h 2604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7912 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7912 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1511, some c1513, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7912 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7912 : lratChecker f7912 p7912 = .success := by decide +kernel
theorem unsat7912 : Unsatisfiable (PosFin 65) f7912 := by
  apply lratCheckerSound f7912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7912
  · intro a ha; simp [p7912] at ha; subst a; trivial
  · exact checked7912
theorem derived7912 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7912 := by
  apply localUnsat_implies_entails f7912 [c1511, c1513] c7912 unsat7912 (by rfl) a
  have h0 : Entails.eval a c1511 := h 1510 (by decide)
  have h1 : Entails.eval a c1513 := h 1512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7913 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7913 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7885, some c7908, some c7912, some c7909, some c7911, some c7910, some c7889, some c601, some c1049, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7913 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7913 : lratChecker f7913 p7913 = .success := by decide +kernel
theorem unsat7913 : Unsatisfiable (PosFin 65) f7913 := by
  apply lratCheckerSound f7913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7913
  · intro a ha; simp [p7913] at ha; subst a; trivial
  · exact checked7913
theorem derived7913 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7913 := by
  apply localUnsat_implies_entails f7913 [c7885, c7908, c7912, c7909, c7911, c7910, c7889, c601, c1049] c7913 unsat7913 (by rfl) a
  have h0 : Entails.eval a c7885 := derived7885 a h
  have h1 : Entails.eval a c7908 := derived7908 a h
  have h2 : Entails.eval a c7912 := derived7912 a h
  have h3 : Entails.eval a c7909 := derived7909 a h
  have h4 : Entails.eval a c7911 := derived7911 a h
  have h5 : Entails.eval a c7910 := derived7910 a h
  have h6 : Entails.eval a c7889 := derived7889 a h
  have h7 : Entails.eval a c601 := h 600 (by decide)
  have h8 : Entails.eval a c1049 := h 1048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7914 : DefaultClause 65 := directClause [(⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7914 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1103, some c2605, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p7914 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7914 : lratChecker f7914 p7914 = .success := by decide +kernel
theorem unsat7914 : Unsatisfiable (PosFin 65) f7914 := by
  apply lratCheckerSound f7914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7914
  · intro a ha; simp [p7914] at ha; subst a; trivial
  · exact checked7914
theorem derived7914 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7914 := by
  apply localUnsat_implies_entails f7914 [c1103, c2605] c7914 unsat7914 (by rfl) a
  have h0 : Entails.eval a c1103 := h 1102 (by decide)
  have h1 : Entails.eval a c2605 := h 2604 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7915 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7915 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7914, some c1481, some c849, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7915 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7915 : lratChecker f7915 p7915 = .success := by decide +kernel
theorem unsat7915 : Unsatisfiable (PosFin 65) f7915 := by
  apply lratCheckerSound f7915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7915
  · intro a ha; simp [p7915] at ha; subst a; trivial
  · exact checked7915
theorem derived7915 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7915 := by
  apply localUnsat_implies_entails f7915 [c7914, c1481, c849] c7915 unsat7915 (by rfl) a
  have h0 : Entails.eval a c7914 := derived7914 a h
  have h1 : Entails.eval a c1481 := h 1480 (by decide)
  have h2 : Entails.eval a c849 := h 848 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7916 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7916 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1507, some c1511, some c1516, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7916 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7916 : lratChecker f7916 p7916 = .success := by decide +kernel
theorem unsat7916 : Unsatisfiable (PosFin 65) f7916 := by
  apply lratCheckerSound f7916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7916
  · intro a ha; simp [p7916] at ha; subst a; trivial
  · exact checked7916
theorem derived7916 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7916 := by
  apply localUnsat_implies_entails f7916 [c1507, c1511, c1516] c7916 unsat7916 (by rfl) a
  have h0 : Entails.eval a c1507 := h 1506 (by decide)
  have h1 : Entails.eval a c1511 := h 1510 (by decide)
  have h2 : Entails.eval a c1516 := h 1515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7917 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7917 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c502, some c537, some c549, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7917 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7917 : lratChecker f7917 p7917 = .success := by decide +kernel
theorem unsat7917 : Unsatisfiable (PosFin 65) f7917 := by
  apply lratCheckerSound f7917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7917
  · intro a ha; simp [p7917] at ha; subst a; trivial
  · exact checked7917
theorem derived7917 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7917 := by
  apply localUnsat_implies_entails f7917 [c502, c537, c549] c7917 unsat7917 (by rfl) a
  have h0 : Entails.eval a c502 := h 501 (by decide)
  have h1 : Entails.eval a c537 := h 536 (by decide)
  have h2 : Entails.eval a c549 := h 548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7918 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7918 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7905, some c7885, some c7908, some c7913, some c7916, some c7915, some c7889, some c7917, some c7910, some c601, some c1049, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7918 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7918 : lratChecker f7918 p7918 = .success := by decide +kernel
theorem unsat7918 : Unsatisfiable (PosFin 65) f7918 := by
  apply lratCheckerSound f7918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7918
  · intro a ha; simp [p7918] at ha; subst a; trivial
  · exact checked7918
theorem derived7918 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7918 := by
  apply localUnsat_implies_entails f7918 [c7905, c7885, c7908, c7913, c7916, c7915, c7889, c7917, c7910, c601, c1049] c7918 unsat7918 (by rfl) a
  have h0 : Entails.eval a c7905 := derived7905 a h
  have h1 : Entails.eval a c7885 := derived7885 a h
  have h2 : Entails.eval a c7908 := derived7908 a h
  have h3 : Entails.eval a c7913 := derived7913 a h
  have h4 : Entails.eval a c7916 := derived7916 a h
  have h5 : Entails.eval a c7915 := derived7915 a h
  have h6 : Entails.eval a c7889 := derived7889 a h
  have h7 : Entails.eval a c7917 := derived7917 a h
  have h8 : Entails.eval a c7910 := derived7910 a h
  have h9 : Entails.eval a c601 := h 600 (by decide)
  have h10 : Entails.eval a c1049 := h 1048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7919 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7919 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1490, some c443, some c636, some c1050, some c828, some c663, some c2052, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7919 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7919 : lratChecker f7919 p7919 = .success := by decide +kernel
theorem unsat7919 : Unsatisfiable (PosFin 65) f7919 := by
  apply lratCheckerSound f7919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7919
  · intro a ha; simp [p7919] at ha; subst a; trivial
  · exact checked7919
theorem derived7919 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7919 := by
  apply localUnsat_implies_entails f7919 [c1490, c443, c636, c1050, c828, c663, c2052] c7919 unsat7919 (by rfl) a
  have h0 : Entails.eval a c1490 := h 1489 (by decide)
  have h1 : Entails.eval a c443 := h 442 (by decide)
  have h2 : Entails.eval a c636 := h 635 (by decide)
  have h3 : Entails.eval a c1050 := h 1049 (by decide)
  have h4 : Entails.eval a c828 := h 827 (by decide)
  have h5 : Entails.eval a c663 := h 662 (by decide)
  have h6 : Entails.eval a c2052 := h 2051 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7920 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7920 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1465, some c1501, some c2669, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7920 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7920 : lratChecker f7920 p7920 = .success := by decide +kernel
theorem unsat7920 : Unsatisfiable (PosFin 65) f7920 := by
  apply lratCheckerSound f7920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7920
  · intro a ha; simp [p7920] at ha; subst a; trivial
  · exact checked7920
theorem derived7920 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7920 := by
  apply localUnsat_implies_entails f7920 [c1465, c1501, c2669] c7920 unsat7920 (by rfl) a
  have h0 : Entails.eval a c1465 := h 1464 (by decide)
  have h1 : Entails.eval a c1501 := h 1500 (by decide)
  have h2 : Entails.eval a c2669 := h 2668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7921 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7921 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1051, some c597, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7921 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7921 : lratChecker f7921 p7921 = .success := by decide +kernel
theorem unsat7921 : Unsatisfiable (PosFin 65) f7921 := by
  apply lratCheckerSound f7921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7921
  · intro a ha; simp [p7921] at ha; subst a; trivial
  · exact checked7921
theorem derived7921 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7921 := by
  apply localUnsat_implies_entails f7921 [c1051, c597] c7921 unsat7921 (by rfl) a
  have h0 : Entails.eval a c1051 := h 1050 (by decide)
  have h1 : Entails.eval a c597 := h 596 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7922 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7922 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c850, some c856, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7922 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7922 : lratChecker f7922 p7922 = .success := by decide +kernel
theorem unsat7922 : Unsatisfiable (PosFin 65) f7922 := by
  apply lratCheckerSound f7922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7922
  · intro a ha; simp [p7922] at ha; subst a; trivial
  · exact checked7922
theorem derived7922 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7922 := by
  apply localUnsat_implies_entails f7922 [c850, c856] c7922 unsat7922 (by rfl) a
  have h0 : Entails.eval a c850 := h 849 (by decide)
  have h1 : Entails.eval a c856 := h 855 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7923 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7923 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1473, some c1496, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7923 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7923 : lratChecker f7923 p7923 = .success := by decide +kernel
theorem unsat7923 : Unsatisfiable (PosFin 65) f7923 := by
  apply lratCheckerSound f7923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7923
  · intro a ha; simp [p7923] at ha; subst a; trivial
  · exact checked7923
theorem derived7923 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7923 := by
  apply localUnsat_implies_entails f7923 [c1473, c1496] c7923 unsat7923 (by rfl) a
  have h0 : Entails.eval a c1473 := h 1472 (by decide)
  have h1 : Entails.eval a c1496 := h 1495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7924 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨20, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7924 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1510, some c1521, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7924 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7924 : lratChecker f7924 p7924 = .success := by decide +kernel
theorem unsat7924 : Unsatisfiable (PosFin 65) f7924 := by
  apply lratCheckerSound f7924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7924
  · intro a ha; simp [p7924] at ha; subst a; trivial
  · exact checked7924
theorem derived7924 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7924 := by
  apply localUnsat_implies_entails f7924 [c1510, c1521] c7924 unsat7924 (by rfl) a
  have h0 : Entails.eval a c1510 := h 1509 (by decide)
  have h1 : Entails.eval a c1521 := h 1520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7925 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7925 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7905, some c7918, some c7919, some c7920, some c7923, some c7924, some c849, some c7922, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7925 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7925 : lratChecker f7925 p7925 = .success := by decide +kernel
theorem unsat7925 : Unsatisfiable (PosFin 65) f7925 := by
  apply lratCheckerSound f7925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7925
  · intro a ha; simp [p7925] at ha; subst a; trivial
  · exact checked7925
theorem derived7925 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7925 := by
  apply localUnsat_implies_entails f7925 [c7905, c7918, c7919, c7920, c7923, c7924, c849, c7922] c7925 unsat7925 (by rfl) a
  have h0 : Entails.eval a c7905 := derived7905 a h
  have h1 : Entails.eval a c7918 := derived7918 a h
  have h2 : Entails.eval a c7919 := derived7919 a h
  have h3 : Entails.eval a c7920 := derived7920 a h
  have h4 : Entails.eval a c7923 := derived7923 a h
  have h5 : Entails.eval a c7924 := derived7924 a h
  have h6 : Entails.eval a c849 := h 848 (by decide)
  have h7 : Entails.eval a c7922 := derived7922 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7926 : DefaultClause 65 := directClause [(⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7926 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7906, some c7889, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7926 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7926 : lratChecker f7926 p7926 = .success := by decide +kernel
theorem unsat7926 : Unsatisfiable (PosFin 65) f7926 := by
  apply lratCheckerSound f7926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7926
  · intro a ha; simp [p7926] at ha; subst a; trivial
  · exact checked7926
theorem derived7926 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7926 := by
  apply localUnsat_implies_entails f7926 [c7906, c7889] c7926 unsat7926 (by rfl) a
  have h0 : Entails.eval a c7906 := derived7906 a h
  have h1 : Entails.eval a c7889 := derived7889 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7927 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨8, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7927 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1386, some c2456, some c2352, some c2186, some c2210, some c2224, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7927 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7927 : lratChecker f7927 p7927 = .success := by decide +kernel
theorem unsat7927 : Unsatisfiable (PosFin 65) f7927 := by
  apply lratCheckerSound f7927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7927
  · intro a ha; simp [p7927] at ha; subst a; trivial
  · exact checked7927
theorem derived7927 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7927 := by
  apply localUnsat_implies_entails f7927 [c1386, c2456, c2352, c2186, c2210, c2224] c7927 unsat7927 (by rfl) a
  have h0 : Entails.eval a c1386 := h 1385 (by decide)
  have h1 : Entails.eval a c2456 := h 2455 (by decide)
  have h2 : Entails.eval a c2352 := h 2351 (by decide)
  have h3 : Entails.eval a c2186 := h 2185 (by decide)
  have h4 : Entails.eval a c2210 := h 2209 (by decide)
  have h5 : Entails.eval a c2224 := h 2223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7928 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7928 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7925, some c7905, some c7885, some c7570, some c7916, some c7574, some c7926, some c7927, some c7909, some c7910, some c601, some c2210, some c2223, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7928 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7928 : lratChecker f7928 p7928 = .success := by decide +kernel
theorem unsat7928 : Unsatisfiable (PosFin 65) f7928 := by
  apply lratCheckerSound f7928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7928
  · intro a ha; simp [p7928] at ha; subst a; trivial
  · exact checked7928
theorem derived7928 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7928 := by
  apply localUnsat_implies_entails f7928 [c7925, c7905, c7885, c7570, c7916, c7574, c7926, c7927, c7909, c7910, c601, c2210, c2223] c7928 unsat7928 (by rfl) a
  have h0 : Entails.eval a c7925 := derived7925 a h
  have h1 : Entails.eval a c7905 := derived7905 a h
  have h2 : Entails.eval a c7885 := derived7885 a h
  have h3 : Entails.eval a c7570 := derived7570 a h
  have h4 : Entails.eval a c7916 := derived7916 a h
  have h5 : Entails.eval a c7574 := derived7574 a h
  have h6 : Entails.eval a c7926 := derived7926 a h
  have h7 : Entails.eval a c7927 := derived7927 a h
  have h8 : Entails.eval a c7909 := derived7909 a h
  have h9 : Entails.eval a c7910 := derived7910 a h
  have h10 : Entails.eval a c601 := h 600 (by decide)
  have h11 : Entails.eval a c2210 := h 2209 (by decide)
  have h12 : Entails.eval a c2223 := h 2222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7929 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7929 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c482, some c478, some c479, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7929 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7929 : lratChecker f7929 p7929 = .success := by decide +kernel
theorem unsat7929 : Unsatisfiable (PosFin 65) f7929 := by
  apply lratCheckerSound f7929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7929
  · intro a ha; simp [p7929] at ha; subst a; trivial
  · exact checked7929
theorem derived7929 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7929 := by
  apply localUnsat_implies_entails f7929 [c482, c478, c479] c7929 unsat7929 (by rfl) a
  have h0 : Entails.eval a c482 := h 481 (by decide)
  have h1 : Entails.eval a c478 := h 477 (by decide)
  have h2 : Entails.eval a c479 := h 478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7930 : DefaultClause 65 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7930 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7582, some c7585, some c2051, some c2044, some c2048, some c1000, some c1006, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7930 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7930 : lratChecker f7930 p7930 = .success := by decide +kernel
theorem unsat7930 : Unsatisfiable (PosFin 65) f7930 := by
  apply lratCheckerSound f7930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7930
  · intro a ha; simp [p7930] at ha; subst a; trivial
  · exact checked7930
theorem derived7930 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7930 := by
  apply localUnsat_implies_entails f7930 [c7582, c7585, c2051, c2044, c2048, c1000, c1006] c7930 unsat7930 (by rfl) a
  have h0 : Entails.eval a c7582 := derived7582 a h
  have h1 : Entails.eval a c7585 := derived7585 a h
  have h2 : Entails.eval a c2051 := h 2050 (by decide)
  have h3 : Entails.eval a c2044 := h 2043 (by decide)
  have h4 : Entails.eval a c2048 := h 2047 (by decide)
  have h5 : Entails.eval a c1000 := h 999 (by decide)
  have h6 : Entails.eval a c1006 := h 1005 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7931 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7931 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c861, some c1489, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7931 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7931 : lratChecker f7931 p7931 = .success := by decide +kernel
theorem unsat7931 : Unsatisfiable (PosFin 65) f7931 := by
  apply lratCheckerSound f7931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7931
  · intro a ha; simp [p7931] at ha; subst a; trivial
  · exact checked7931
theorem derived7931 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7931 := by
  apply localUnsat_implies_entails f7931 [c861, c1489] c7931 unsat7931 (by rfl) a
  have h0 : Entails.eval a c861 := h 860 (by decide)
  have h1 : Entails.eval a c1489 := h 1488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7932 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7932 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1386, some c1615, some c1003, some c7910, some c7931, some c1251, some c451, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7932 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7932 : lratChecker f7932 p7932 = .success := by decide +kernel
theorem unsat7932 : Unsatisfiable (PosFin 65) f7932 := by
  apply lratCheckerSound f7932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7932
  · intro a ha; simp [p7932] at ha; subst a; trivial
  · exact checked7932
theorem derived7932 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7932 := by
  apply localUnsat_implies_entails f7932 [c1386, c1615, c1003, c7910, c7931, c1251, c451] c7932 unsat7932 (by rfl) a
  have h0 : Entails.eval a c1386 := h 1385 (by decide)
  have h1 : Entails.eval a c1615 := h 1614 (by decide)
  have h2 : Entails.eval a c1003 := h 1002 (by decide)
  have h3 : Entails.eval a c7910 := derived7910 a h
  have h4 : Entails.eval a c7931 := derived7931 a h
  have h5 : Entails.eval a c1251 := h 1250 (by decide)
  have h6 : Entails.eval a c451 := h 450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7933 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7933 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7925, some c7905, some c7885, some c7570, some c7916, some c7574, some c7928, some c7930, some c7932, some c7909, some c7910, some c7931, some c1623, some c1251, some c451, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7933 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7933 : lratChecker f7933 p7933 = .success := by decide +kernel
theorem unsat7933 : Unsatisfiable (PosFin 65) f7933 := by
  apply lratCheckerSound f7933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7933
  · intro a ha; simp [p7933] at ha; subst a; trivial
  · exact checked7933
theorem derived7933 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7933 := by
  apply localUnsat_implies_entails f7933 [c7925, c7905, c7885, c7570, c7916, c7574, c7928, c7930, c7932, c7909, c7910, c7931, c1623, c1251, c451] c7933 unsat7933 (by rfl) a
  have h0 : Entails.eval a c7925 := derived7925 a h
  have h1 : Entails.eval a c7905 := derived7905 a h
  have h2 : Entails.eval a c7885 := derived7885 a h
  have h3 : Entails.eval a c7570 := derived7570 a h
  have h4 : Entails.eval a c7916 := derived7916 a h
  have h5 : Entails.eval a c7574 := derived7574 a h
  have h6 : Entails.eval a c7928 := derived7928 a h
  have h7 : Entails.eval a c7930 := derived7930 a h
  have h8 : Entails.eval a c7932 := derived7932 a h
  have h9 : Entails.eval a c7909 := derived7909 a h
  have h10 : Entails.eval a c7910 := derived7910 a h
  have h11 : Entails.eval a c7931 := derived7931 a h
  have h12 : Entails.eval a c1623 := h 1622 (by decide)
  have h13 : Entails.eval a c1251 := h 1250 (by decide)
  have h14 : Entails.eval a c451 := h 450 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7934 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7934 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7925, some c7905, some c7885, some c7570, some c7916, some c7574, some c1386, some c7932, some c1003, some c7585, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7934 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked7934 : lratChecker f7934 p7934 = .success := by decide +kernel
theorem unsat7934 : Unsatisfiable (PosFin 65) f7934 := by
  apply lratCheckerSound f7934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7934
  · intro a ha; simp [p7934] at ha; subst a; trivial
  · exact checked7934
theorem derived7934 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7934 := by
  apply localUnsat_implies_entails f7934 [c7925, c7905, c7885, c7570, c7916, c7574, c1386, c7932, c1003, c7585] c7934 unsat7934 (by rfl) a
  have h0 : Entails.eval a c7925 := derived7925 a h
  have h1 : Entails.eval a c7905 := derived7905 a h
  have h2 : Entails.eval a c7885 := derived7885 a h
  have h3 : Entails.eval a c7570 := derived7570 a h
  have h4 : Entails.eval a c7916 := derived7916 a h
  have h5 : Entails.eval a c7574 := derived7574 a h
  have h6 : Entails.eval a c1386 := h 1385 (by decide)
  have h7 : Entails.eval a c7932 := derived7932 a h
  have h8 : Entails.eval a c1003 := h 1002 (by decide)
  have h9 : Entails.eval a c7585 := derived7585 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7935 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨30, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7935 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7917, some c7926, some c7910, some c601, some c7931, some c2223, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7935 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7935 : lratChecker f7935 p7935 = .success := by decide +kernel
theorem unsat7935 : Unsatisfiable (PosFin 65) f7935 := by
  apply lratCheckerSound f7935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7935
  · intro a ha; simp [p7935] at ha; subst a; trivial
  · exact checked7935
theorem derived7935 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7935 := by
  apply localUnsat_implies_entails f7935 [c7917, c7926, c7910, c601, c7931, c2223] c7935 unsat7935 (by rfl) a
  have h0 : Entails.eval a c7917 := derived7917 a h
  have h1 : Entails.eval a c7926 := derived7926 a h
  have h2 : Entails.eval a c7910 := derived7910 a h
  have h3 : Entails.eval a c601 := h 600 (by decide)
  have h4 : Entails.eval a c7931 := derived7931 a h
  have h5 : Entails.eval a c2223 := h 2222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7936 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7936 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1481, some c448, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7936 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7936 : lratChecker f7936 p7936 = .success := by decide +kernel
theorem unsat7936 : Unsatisfiable (PosFin 65) f7936 := by
  apply lratCheckerSound f7936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7936
  · intro a ha; simp [p7936] at ha; subst a; trivial
  · exact checked7936
theorem derived7936 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7936 := by
  apply localUnsat_implies_entails f7936 [c1481, c448] c7936 unsat7936 (by rfl) a
  have h0 : Entails.eval a c1481 := h 1480 (by decide)
  have h1 : Entails.eval a c448 := h 447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7937 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7937 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7925, some c7905, some c7885, some c7916, some c7570, some c7574, some c7933, some c7934, some c7935, some c7930, some c7936, some c7922, some c7931, some c1496, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7937 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7937 : lratChecker f7937 p7937 = .success := by decide +kernel
theorem unsat7937 : Unsatisfiable (PosFin 65) f7937 := by
  apply lratCheckerSound f7937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7937
  · intro a ha; simp [p7937] at ha; subst a; trivial
  · exact checked7937
theorem derived7937 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7937 := by
  apply localUnsat_implies_entails f7937 [c7925, c7905, c7885, c7916, c7570, c7574, c7933, c7934, c7935, c7930, c7936, c7922, c7931, c1496] c7937 unsat7937 (by rfl) a
  have h0 : Entails.eval a c7925 := derived7925 a h
  have h1 : Entails.eval a c7905 := derived7905 a h
  have h2 : Entails.eval a c7885 := derived7885 a h
  have h3 : Entails.eval a c7916 := derived7916 a h
  have h4 : Entails.eval a c7570 := derived7570 a h
  have h5 : Entails.eval a c7574 := derived7574 a h
  have h6 : Entails.eval a c7933 := derived7933 a h
  have h7 : Entails.eval a c7934 := derived7934 a h
  have h8 : Entails.eval a c7935 := derived7935 a h
  have h9 : Entails.eval a c7930 := derived7930 a h
  have h10 : Entails.eval a c7936 := derived7936 a h
  have h11 : Entails.eval a c7922 := derived7922 a h
  have h12 : Entails.eval a c7931 := derived7931 a h
  have h13 : Entails.eval a c1496 := h 1495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7938 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7938 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7905, some c7925, some c7937, some c7920, some c7923, some c7924, some c1223, some c1233, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7938 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7938 : lratChecker f7938 p7938 = .success := by decide +kernel
theorem unsat7938 : Unsatisfiable (PosFin 65) f7938 := by
  apply lratCheckerSound f7938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7938
  · intro a ha; simp [p7938] at ha; subst a; trivial
  · exact checked7938
theorem derived7938 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7938 := by
  apply localUnsat_implies_entails f7938 [c7905, c7925, c7937, c7920, c7923, c7924, c1223, c1233] c7938 unsat7938 (by rfl) a
  have h0 : Entails.eval a c7905 := derived7905 a h
  have h1 : Entails.eval a c7925 := derived7925 a h
  have h2 : Entails.eval a c7937 := derived7937 a h
  have h3 : Entails.eval a c7920 := derived7920 a h
  have h4 : Entails.eval a c7923 := derived7923 a h
  have h5 : Entails.eval a c7924 := derived7924 a h
  have h6 : Entails.eval a c1223 := h 1222 (by decide)
  have h7 : Entails.eval a c1233 := h 1232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7939 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7939 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7887, some c7938, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7939 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7939 : lratChecker f7939 p7939 = .success := by decide +kernel
theorem unsat7939 : Unsatisfiable (PosFin 65) f7939 := by
  apply lratCheckerSound f7939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7939
  · intro a ha; simp [p7939] at ha; subst a; trivial
  · exact checked7939
theorem derived7939 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7939 := by
  apply localUnsat_implies_entails f7939 [c7849, c7887, c7938] c7939 unsat7939 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7887 := derived7887 a h
  have h2 : Entails.eval a c7938 := derived7938 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7940 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7940 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2943, some c2948, some c2946, some c2934, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p7940 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7940 : lratChecker f7940 p7940 = .success := by decide +kernel
theorem unsat7940 : Unsatisfiable (PosFin 65) f7940 := by
  apply lratCheckerSound f7940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7940
  · intro a ha; simp [p7940] at ha; subst a; trivial
  · exact checked7940
theorem derived7940 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7940 := by
  apply localUnsat_implies_entails f7940 [c2943, c2948, c2946, c2934] c7940 unsat7940 (by rfl) a
  have h0 : Entails.eval a c2943 := h 2942 (by decide)
  have h1 : Entails.eval a c2948 := h 2947 (by decide)
  have h2 : Entails.eval a c2946 := h 2945 (by decide)
  have h3 : Entails.eval a c2934 := h 2933 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7941 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7941 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7940, some c2936, some c2947, some c2950, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7941 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7941 : lratChecker f7941 p7941 = .success := by decide +kernel
theorem unsat7941 : Unsatisfiable (PosFin 65) f7941 := by
  apply lratCheckerSound f7941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7941
  · intro a ha; simp [p7941] at ha; subst a; trivial
  · exact checked7941
theorem derived7941 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7941 := by
  apply localUnsat_implies_entails f7941 [c7940, c2936, c2947, c2950] c7941 unsat7941 (by rfl) a
  have h0 : Entails.eval a c7940 := derived7940 a h
  have h1 : Entails.eval a c2936 := h 2935 (by decide)
  have h2 : Entails.eval a c2947 := h 2946 (by decide)
  have h3 : Entails.eval a c2950 := h 2949 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7942 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7942 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2289, some c1332, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7942 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7942 : lratChecker f7942 p7942 = .success := by decide +kernel
theorem unsat7942 : Unsatisfiable (PosFin 65) f7942 := by
  apply lratCheckerSound f7942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7942
  · intro a ha; simp [p7942] at ha; subst a; trivial
  · exact checked7942
theorem derived7942 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7942 := by
  apply localUnsat_implies_entails f7942 [c2289, c1332] c7942 unsat7942 (by rfl) a
  have h0 : Entails.eval a c2289 := h 2288 (by decide)
  have h1 : Entails.eval a c1332 := h 1331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7943 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7943 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7942, some c7874, some c1563, some c1558, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7943 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7943 : lratChecker f7943 p7943 = .success := by decide +kernel
theorem unsat7943 : Unsatisfiable (PosFin 65) f7943 := by
  apply lratCheckerSound f7943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7943
  · intro a ha; simp [p7943] at ha; subst a; trivial
  · exact checked7943
theorem derived7943 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7943 := by
  apply localUnsat_implies_entails f7943 [c7942, c7874, c1563, c1558] c7943 unsat7943 (by rfl) a
  have h0 : Entails.eval a c7942 := derived7942 a h
  have h1 : Entails.eval a c7874 := derived7874 a h
  have h2 : Entails.eval a c1563 := h 1562 (by decide)
  have h3 : Entails.eval a c1558 := h 1557 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7944 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7944 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7943, some c1174, some c1177, some c1187, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7944 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7944 : lratChecker f7944 p7944 = .success := by decide +kernel
theorem unsat7944 : Unsatisfiable (PosFin 65) f7944 := by
  apply lratCheckerSound f7944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7944
  · intro a ha; simp [p7944] at ha; subst a; trivial
  · exact checked7944
theorem derived7944 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7944 := by
  apply localUnsat_implies_entails f7944 [c7943, c1174, c1177, c1187] c7944 unsat7944 (by rfl) a
  have h0 : Entails.eval a c7943 := derived7943 a h
  have h1 : Entails.eval a c1174 := h 1173 (by decide)
  have h2 : Entails.eval a c1177 := h 1176 (by decide)
  have h3 : Entails.eval a c1187 := h 1186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7945 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7945 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1282, some c1347, some c1332, some c1897, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7945 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7945 : lratChecker f7945 p7945 = .success := by decide +kernel
theorem unsat7945 : Unsatisfiable (PosFin 65) f7945 := by
  apply lratCheckerSound f7945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7945
  · intro a ha; simp [p7945] at ha; subst a; trivial
  · exact checked7945
theorem derived7945 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7945 := by
  apply localUnsat_implies_entails f7945 [c1282, c1347, c1332, c1897] c7945 unsat7945 (by rfl) a
  have h0 : Entails.eval a c1282 := h 1281 (by decide)
  have h1 : Entails.eval a c1347 := h 1346 (by decide)
  have h2 : Entails.eval a c1332 := h 1331 (by decide)
  have h3 : Entails.eval a c1897 := h 1896 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7946 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7946 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1417, some c1278, some c1343, some c1962, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p7946 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7946 : lratChecker f7946 p7946 = .success := by decide +kernel
theorem unsat7946 : Unsatisfiable (PosFin 65) f7946 := by
  apply lratCheckerSound f7946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7946
  · intro a ha; simp [p7946] at ha; subst a; trivial
  · exact checked7946
theorem derived7946 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7946 := by
  apply localUnsat_implies_entails f7946 [c1417, c1278, c1343, c1962] c7946 unsat7946 (by rfl) a
  have h0 : Entails.eval a c1417 := h 1416 (by decide)
  have h1 : Entails.eval a c1278 := h 1277 (by decide)
  have h2 : Entails.eval a c1343 := h 1342 (by decide)
  have h3 : Entails.eval a c1962 := h 1961 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7947 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7947 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7946, some c7945, some c601, some c1563, some c1049, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7947 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7947 : lratChecker f7947 p7947 = .success := by decide +kernel
theorem unsat7947 : Unsatisfiable (PosFin 65) f7947 := by
  apply lratCheckerSound f7947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7947
  · intro a ha; simp [p7947] at ha; subst a; trivial
  · exact checked7947
theorem derived7947 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7947 := by
  apply localUnsat_implies_entails f7947 [c7946, c7945, c601, c1563, c1049] c7947 unsat7947 (by rfl) a
  have h0 : Entails.eval a c7946 := derived7946 a h
  have h1 : Entails.eval a c7945 := derived7945 a h
  have h2 : Entails.eval a c601 := h 600 (by decide)
  have h3 : Entails.eval a c1563 := h 1562 (by decide)
  have h4 : Entails.eval a c1049 := h 1048 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7948 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7948 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7944, some c7946, some c7947, some c7597, some c7907, some c2412, some c1441, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7948 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7948 : lratChecker f7948 p7948 = .success := by decide +kernel
theorem unsat7948 : Unsatisfiable (PosFin 65) f7948 := by
  apply lratCheckerSound f7948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7948
  · intro a ha; simp [p7948] at ha; subst a; trivial
  · exact checked7948
theorem derived7948 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7948 := by
  apply localUnsat_implies_entails f7948 [c7944, c7946, c7947, c7597, c7907, c2412, c1441] c7948 unsat7948 (by rfl) a
  have h0 : Entails.eval a c7944 := derived7944 a h
  have h1 : Entails.eval a c7946 := derived7946 a h
  have h2 : Entails.eval a c7947 := derived7947 a h
  have h3 : Entails.eval a c7597 := derived7597 a h
  have h4 : Entails.eval a c7907 := derived7907 a h
  have h5 : Entails.eval a c2412 := h 2411 (by decide)
  have h6 : Entails.eval a c1441 := h 1440 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7949 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7949 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7941, some c7948, some c7579, some c7632, some c7942, some c605, some c884, some c1975, some c2009, some c2521, some c2542, some c7577, some c899, some c1146, some c2317, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7949 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked7949 : lratChecker f7949 p7949 = .success := by decide +kernel
theorem unsat7949 : Unsatisfiable (PosFin 65) f7949 := by
  apply lratCheckerSound f7949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7949
  · intro a ha; simp [p7949] at ha; subst a; trivial
  · exact checked7949
theorem derived7949 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7949 := by
  apply localUnsat_implies_entails f7949 [c7849, c7941, c7948, c7579, c7632, c7942, c605, c884, c1975, c2009, c2521, c2542, c7577, c899, c1146, c2317] c7949 unsat7949 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7941 := derived7941 a h
  have h2 : Entails.eval a c7948 := derived7948 a h
  have h3 : Entails.eval a c7579 := derived7579 a h
  have h4 : Entails.eval a c7632 := derived7632 a h
  have h5 : Entails.eval a c7942 := derived7942 a h
  have h6 : Entails.eval a c605 := h 604 (by decide)
  have h7 : Entails.eval a c884 := h 883 (by decide)
  have h8 : Entails.eval a c1975 := h 1974 (by decide)
  have h9 : Entails.eval a c2009 := h 2008 (by decide)
  have h10 : Entails.eval a c2521 := h 2520 (by decide)
  have h11 : Entails.eval a c2542 := h 2541 (by decide)
  have h12 : Entails.eval a c7577 := derived7577 a h
  have h13 : Entails.eval a c899 := h 898 (by decide)
  have h14 : Entails.eval a c1146 := h 1145 (by decide)
  have h15 : Entails.eval a c2317 := h 2316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7950 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7950 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2289, some c907, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7950 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7950 : lratChecker f7950 p7950 = .success := by decide +kernel
theorem unsat7950 : Unsatisfiable (PosFin 65) f7950 := by
  apply lratCheckerSound f7950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7950
  · intro a ha; simp [p7950] at ha; subst a; trivial
  · exact checked7950
theorem derived7950 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7950 := by
  apply localUnsat_implies_entails f7950 [c2289, c907] c7950 unsat7950 (by rfl) a
  have h0 : Entails.eval a c2289 := h 2288 (by decide)
  have h1 : Entails.eval a c907 := h 906 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7951 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7951 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7941, some c7948, some c7579, some c7632, some c7949, some c7950, some c884, some c2554, some c2175, some c686, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7951 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked7951 : lratChecker f7951 p7951 = .success := by decide +kernel
theorem unsat7951 : Unsatisfiable (PosFin 65) f7951 := by
  apply lratCheckerSound f7951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7951
  · intro a ha; simp [p7951] at ha; subst a; trivial
  · exact checked7951
theorem derived7951 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7951 := by
  apply localUnsat_implies_entails f7951 [c7849, c7941, c7948, c7579, c7632, c7949, c7950, c884, c2554, c2175, c686] c7951 unsat7951 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7941 := derived7941 a h
  have h2 : Entails.eval a c7948 := derived7948 a h
  have h3 : Entails.eval a c7579 := derived7579 a h
  have h4 : Entails.eval a c7632 := derived7632 a h
  have h5 : Entails.eval a c7949 := derived7949 a h
  have h6 : Entails.eval a c7950 := derived7950 a h
  have h7 : Entails.eval a c884 := h 883 (by decide)
  have h8 : Entails.eval a c2554 := h 2553 (by decide)
  have h9 : Entails.eval a c2175 := h 2174 (by decide)
  have h10 : Entails.eval a c686 := h 685 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7952 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7952 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7939, some c7951, some c7765, some c2899, some c2900, some c2901, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7952 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7952 : lratChecker f7952 p7952 = .success := by decide +kernel
theorem unsat7952 : Unsatisfiable (PosFin 65) f7952 := by
  apply lratCheckerSound f7952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7952
  · intro a ha; simp [p7952] at ha; subst a; trivial
  · exact checked7952
theorem derived7952 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7952 := by
  apply localUnsat_implies_entails f7952 [c7939, c7951, c7765, c2899, c2900, c2901] c7952 unsat7952 (by rfl) a
  have h0 : Entails.eval a c7939 := derived7939 a h
  have h1 : Entails.eval a c7951 := derived7951 a h
  have h2 : Entails.eval a c7765 := derived7765 a h
  have h3 : Entails.eval a c2899 := h 2898 (by decide)
  have h4 : Entails.eval a c2900 := h 2899 (by decide)
  have h5 : Entails.eval a c2901 := h 2900 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7953 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7953 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c925, some c929, some c926, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7953 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7953 : lratChecker f7953 p7953 = .success := by decide +kernel
theorem unsat7953 : Unsatisfiable (PosFin 65) f7953 := by
  apply lratCheckerSound f7953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7953
  · intro a ha; simp [p7953] at ha; subst a; trivial
  · exact checked7953
theorem derived7953 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7953 := by
  apply localUnsat_implies_entails f7953 [c925, c929, c926] c7953 unsat7953 (by rfl) a
  have h0 : Entails.eval a c925 := h 924 (by decide)
  have h1 : Entails.eval a c929 := h 928 (by decide)
  have h2 : Entails.eval a c926 := h 925 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7954 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7954 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7632, some c2285, some c2292, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7954 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7954 : lratChecker f7954 p7954 = .success := by decide +kernel
theorem unsat7954 : Unsatisfiable (PosFin 65) f7954 := by
  apply lratCheckerSound f7954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7954
  · intro a ha; simp [p7954] at ha; subst a; trivial
  · exact checked7954
theorem derived7954 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7954 := by
  apply localUnsat_implies_entails f7954 [c7632, c2285, c2292] c7954 unsat7954 (by rfl) a
  have h0 : Entails.eval a c7632 := derived7632 a h
  have h1 : Entails.eval a c2285 := h 2284 (by decide)
  have h2 : Entails.eval a c2292 := h 2291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7955 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7955 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7952, some c7939, some c7849, some c7941, some c7948, some c7592, some c7953, some c7954, some c7586, some c7583, some c7615, some c1158, some c2323, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7955 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7955 : lratChecker f7955 p7955 = .success := by decide +kernel
theorem unsat7955 : Unsatisfiable (PosFin 65) f7955 := by
  apply lratCheckerSound f7955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7955
  · intro a ha; simp [p7955] at ha; subst a; trivial
  · exact checked7955
theorem derived7955 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7955 := by
  apply localUnsat_implies_entails f7955 [c7952, c7939, c7849, c7941, c7948, c7592, c7953, c7954, c7586, c7583, c7615, c1158, c2323] c7955 unsat7955 (by rfl) a
  have h0 : Entails.eval a c7952 := derived7952 a h
  have h1 : Entails.eval a c7939 := derived7939 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c7941 := derived7941 a h
  have h4 : Entails.eval a c7948 := derived7948 a h
  have h5 : Entails.eval a c7592 := derived7592 a h
  have h6 : Entails.eval a c7953 := derived7953 a h
  have h7 : Entails.eval a c7954 := derived7954 a h
  have h8 : Entails.eval a c7586 := derived7586 a h
  have h9 : Entails.eval a c7583 := derived7583 a h
  have h10 : Entails.eval a c7615 := derived7615 a h
  have h11 : Entails.eval a c1158 := h 1157 (by decide)
  have h12 : Entails.eval a c2323 := h 2322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7956 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7956 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7680, some c1295, some c1363, some c2438, some c7130, some c536, some c537, some c549, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7956 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7956 : lratChecker f7956 p7956 = .success := by decide +kernel
theorem unsat7956 : Unsatisfiable (PosFin 65) f7956 := by
  apply lratCheckerSound f7956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7956
  · intro a ha; simp [p7956] at ha; subst a; trivial
  · exact checked7956
theorem derived7956 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7956 := by
  apply localUnsat_implies_entails f7956 [c7680, c1295, c1363, c2438, c7130, c536, c537, c549] c7956 unsat7956 (by rfl) a
  have h0 : Entails.eval a c7680 := derived7680 a h
  have h1 : Entails.eval a c1295 := h 1294 (by decide)
  have h2 : Entails.eval a c1363 := h 1362 (by decide)
  have h3 : Entails.eval a c2438 := h 2437 (by decide)
  have h4 : Entails.eval a c7130 := derived7130 a h
  have h5 : Entails.eval a c536 := h 535 (by decide)
  have h6 : Entails.eval a c537 := h 536 (by decide)
  have h7 : Entails.eval a c549 := h 548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7957 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7957 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7956, some c7895, some c7953, some c2282, some c2301, some c2296, some c2292, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7957 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7957 : lratChecker f7957 p7957 = .success := by decide +kernel
theorem unsat7957 : Unsatisfiable (PosFin 65) f7957 := by
  apply lratCheckerSound f7957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7957
  · intro a ha; simp [p7957] at ha; subst a; trivial
  · exact checked7957
theorem derived7957 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7957 := by
  apply localUnsat_implies_entails f7957 [c7956, c7895, c7953, c2282, c2301, c2296, c2292] c7957 unsat7957 (by rfl) a
  have h0 : Entails.eval a c7956 := derived7956 a h
  have h1 : Entails.eval a c7895 := derived7895 a h
  have h2 : Entails.eval a c7953 := derived7953 a h
  have h3 : Entails.eval a c2282 := h 2281 (by decide)
  have h4 : Entails.eval a c2301 := h 2300 (by decide)
  have h5 : Entails.eval a c2296 := h 2295 (by decide)
  have h6 : Entails.eval a c2292 := h 2291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7958 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7958 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1324, some c1338, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7958 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7958 : lratChecker f7958 p7958 = .success := by decide +kernel
theorem unsat7958 : Unsatisfiable (PosFin 65) f7958 := by
  apply lratCheckerSound f7958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7958
  · intro a ha; simp [p7958] at ha; subst a; trivial
  · exact checked7958
theorem derived7958 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7958 := by
  apply localUnsat_implies_entails f7958 [c1324, c1338] c7958 unsat7958 (by rfl) a
  have h0 : Entails.eval a c1324 := h 1323 (by decide)
  have h1 : Entails.eval a c1338 := h 1337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7959 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7959 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1168, some c7899, some c1179, some c7504, some c2543, some c558, some c2408, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7959 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7959 : lratChecker f7959 p7959 = .success := by decide +kernel
theorem unsat7959 : Unsatisfiable (PosFin 65) f7959 := by
  apply lratCheckerSound f7959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7959
  · intro a ha; simp [p7959] at ha; subst a; trivial
  · exact checked7959
theorem derived7959 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7959 := by
  apply localUnsat_implies_entails f7959 [c1168, c7899, c1179, c7504, c2543, c558, c2408] c7959 unsat7959 (by rfl) a
  have h0 : Entails.eval a c1168 := h 1167 (by decide)
  have h1 : Entails.eval a c7899 := derived7899 a h
  have h2 : Entails.eval a c1179 := h 1178 (by decide)
  have h3 : Entails.eval a c7504 := derived7504 a h
  have h4 : Entails.eval a c2543 := h 2542 (by decide)
  have h5 : Entails.eval a c558 := h 557 (by decide)
  have h6 : Entails.eval a c2408 := h 2407 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7960 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7960 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7957, some c7959, some c7926, some c7958, some c7898, some c2356, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7960 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7960 : lratChecker f7960 p7960 = .success := by decide +kernel
theorem unsat7960 : Unsatisfiable (PosFin 65) f7960 := by
  apply lratCheckerSound f7960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7960
  · intro a ha; simp [p7960] at ha; subst a; trivial
  · exact checked7960
theorem derived7960 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7960 := by
  apply localUnsat_implies_entails f7960 [c7957, c7959, c7926, c7958, c7898, c2356] c7960 unsat7960 (by rfl) a
  have h0 : Entails.eval a c7957 := derived7957 a h
  have h1 : Entails.eval a c7959 := derived7959 a h
  have h2 : Entails.eval a c7926 := derived7926 a h
  have h3 : Entails.eval a c7958 := derived7958 a h
  have h4 : Entails.eval a c7898 := derived7898 a h
  have h5 : Entails.eval a c2356 := h 2355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7961 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7961 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c536, some c537, some c549, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7961 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7961 : lratChecker f7961 p7961 = .success := by decide +kernel
theorem unsat7961 : Unsatisfiable (PosFin 65) f7961 := by
  apply lratCheckerSound f7961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7961
  · intro a ha; simp [p7961] at ha; subst a; trivial
  · exact checked7961
theorem derived7961 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7961 := by
  apply localUnsat_implies_entails f7961 [c536, c537, c549] c7961 unsat7961 (by rfl) a
  have h0 : Entails.eval a c536 := h 535 (by decide)
  have h1 : Entails.eval a c537 := h 536 (by decide)
  have h2 : Entails.eval a c549 := h 548 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7962 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7962 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7443, some c946, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7962 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7962 : lratChecker f7962 p7962 = .success := by decide +kernel
theorem unsat7962 : Unsatisfiable (PosFin 65) f7962 := by
  apply lratCheckerSound f7962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7962
  · intro a ha; simp [p7962] at ha; subst a; trivial
  · exact checked7962
theorem derived7962 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7962 := by
  apply localUnsat_implies_entails f7962 [c7443, c946] c7962 unsat7962 (by rfl) a
  have h0 : Entails.eval a c7443 := derived7443 a h
  have h1 : Entails.eval a c946 := h 945 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7963 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7963 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1096, some c1317, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p7963 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7963 : lratChecker f7963 p7963 = .success := by decide +kernel
theorem unsat7963 : Unsatisfiable (PosFin 65) f7963 := by
  apply lratCheckerSound f7963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7963
  · intro a ha; simp [p7963] at ha; subst a; trivial
  · exact checked7963
theorem derived7963 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7963 := by
  apply localUnsat_implies_entails f7963 [c1096, c1317] c7963 unsat7963 (by rfl) a
  have h0 : Entails.eval a c1096 := h 1095 (by decide)
  have h1 : Entails.eval a c1317 := h 1316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7964 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨28, by decide⟩, true), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7964 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1321, some c1107, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7964 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7964 : lratChecker f7964 p7964 = .success := by decide +kernel
theorem unsat7964 : Unsatisfiable (PosFin 65) f7964 := by
  apply lratCheckerSound f7964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7964
  · intro a ha; simp [p7964] at ha; subst a; trivial
  · exact checked7964
theorem derived7964 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7964 := by
  apply localUnsat_implies_entails f7964 [c1321, c1107] c7964 unsat7964 (by rfl) a
  have h0 : Entails.eval a c1321 := h 1320 (by decide)
  have h1 : Entails.eval a c1107 := h 1106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7965 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7965 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7680, some c7849, some c7958, some c7961, some c7962, some c7963, some c7964, some c1294, some c2166, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7965 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7965 : lratChecker f7965 p7965 = .success := by decide +kernel
theorem unsat7965 : Unsatisfiable (PosFin 65) f7965 := by
  apply lratCheckerSound f7965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7965
  · intro a ha; simp [p7965] at ha; subst a; trivial
  · exact checked7965
theorem derived7965 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7965 := by
  apply localUnsat_implies_entails f7965 [c7680, c7849, c7958, c7961, c7962, c7963, c7964, c1294, c2166] c7965 unsat7965 (by rfl) a
  have h0 : Entails.eval a c7680 := derived7680 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c7958 := derived7958 a h
  have h3 : Entails.eval a c7961 := derived7961 a h
  have h4 : Entails.eval a c7962 := derived7962 a h
  have h5 : Entails.eval a c7963 := derived7963 a h
  have h6 : Entails.eval a c7964 := derived7964 a h
  have h7 : Entails.eval a c1294 := h 1293 (by decide)
  have h8 : Entails.eval a c2166 := h 2165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7966 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7966 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1373, some c1048, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p7966 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7966 : lratChecker f7966 p7966 = .success := by decide +kernel
theorem unsat7966 : Unsatisfiable (PosFin 65) f7966 := by
  apply lratCheckerSound f7966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7966
  · intro a ha; simp [p7966] at ha; subst a; trivial
  · exact checked7966
theorem derived7966 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7966 := by
  apply localUnsat_implies_entails f7966 [c1373, c1048] c7966 unsat7966 (by rfl) a
  have h0 : Entails.eval a c1373 := h 1372 (by decide)
  have h1 : Entails.eval a c1048 := h 1047 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7967 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7967 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7926, some c7921, some c7966, some c2220, some c609, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7967 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked7967 : lratChecker f7967 p7967 = .success := by decide +kernel
theorem unsat7967 : Unsatisfiable (PosFin 65) f7967 := by
  apply lratCheckerSound f7967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7967
  · intro a ha; simp [p7967] at ha; subst a; trivial
  · exact checked7967
theorem derived7967 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7967 := by
  apply localUnsat_implies_entails f7967 [c7926, c7921, c7966, c2220, c609] c7967 unsat7967 (by rfl) a
  have h0 : Entails.eval a c7926 := derived7926 a h
  have h1 : Entails.eval a c7921 := derived7921 a h
  have h2 : Entails.eval a c7966 := derived7966 a h
  have h3 : Entails.eval a c2220 := h 2219 (by decide)
  have h4 : Entails.eval a c609 := h 608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c7968 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7968 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2188, some c2314, some c635, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7968 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7968 : lratChecker f7968 p7968 = .success := by decide +kernel
theorem unsat7968 : Unsatisfiable (PosFin 65) f7968 := by
  apply lratCheckerSound f7968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7968
  · intro a ha; simp [p7968] at ha; subst a; trivial
  · exact checked7968
theorem derived7968 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7968 := by
  apply localUnsat_implies_entails f7968 [c2188, c2314, c635] c7968 unsat7968 (by rfl) a
  have h0 : Entails.eval a c2188 := h 2187 (by decide)
  have h1 : Entails.eval a c2314 := h 2313 (by decide)
  have h2 : Entails.eval a c635 := h 634 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7969 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7969 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7939, some c7952, some c7955, some c7957, some c7960, some c7680, some c7965, some c7967, some c7962, some c7968, some c2344, some c2204, some c628, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7969 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7969 : lratChecker f7969 p7969 = .success := by decide +kernel
theorem unsat7969 : Unsatisfiable (PosFin 65) f7969 := by
  apply lratCheckerSound f7969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7969
  · intro a ha; simp [p7969] at ha; subst a; trivial
  · exact checked7969
theorem derived7969 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7969 := by
  apply localUnsat_implies_entails f7969 [c7849, c7939, c7952, c7955, c7957, c7960, c7680, c7965, c7967, c7962, c7968, c2344, c2204, c628] c7969 unsat7969 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7939 := derived7939 a h
  have h2 : Entails.eval a c7952 := derived7952 a h
  have h3 : Entails.eval a c7955 := derived7955 a h
  have h4 : Entails.eval a c7957 := derived7957 a h
  have h5 : Entails.eval a c7960 := derived7960 a h
  have h6 : Entails.eval a c7680 := derived7680 a h
  have h7 : Entails.eval a c7965 := derived7965 a h
  have h8 : Entails.eval a c7967 := derived7967 a h
  have h9 : Entails.eval a c7962 := derived7962 a h
  have h10 : Entails.eval a c7968 := derived7968 a h
  have h11 : Entails.eval a c2344 := h 2343 (by decide)
  have h12 : Entails.eval a c2204 := h 2203 (by decide)
  have h13 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7970 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7970 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7953, some c2310, some c2279, some c2307, some c7683, some c7968, some c2334, some c1152, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7970 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7970 : lratChecker f7970 p7970 = .success := by decide +kernel
theorem unsat7970 : Unsatisfiable (PosFin 65) f7970 := by
  apply lratCheckerSound f7970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7970
  · intro a ha; simp [p7970] at ha; subst a; trivial
  · exact checked7970
theorem derived7970 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7970 := by
  apply localUnsat_implies_entails f7970 [c7953, c2310, c2279, c2307, c7683, c7968, c2334, c1152] c7970 unsat7970 (by rfl) a
  have h0 : Entails.eval a c7953 := derived7953 a h
  have h1 : Entails.eval a c2310 := h 2309 (by decide)
  have h2 : Entails.eval a c2279 := h 2278 (by decide)
  have h3 : Entails.eval a c2307 := h 2306 (by decide)
  have h4 : Entails.eval a c7683 := derived7683 a h
  have h5 : Entails.eval a c7968 := derived7968 a h
  have h6 : Entails.eval a c2334 := h 2333 (by decide)
  have h7 : Entails.eval a c1152 := h 1151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7971 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7971 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7939, some c7952, some c7955, some c7957, some c7969, some c7592, some c7953, some c7130, some c7970, some c7680, some c7596, some c7968, some c2344, some c628, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7971 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7971 : lratChecker f7971 p7971 = .success := by decide +kernel
theorem unsat7971 : Unsatisfiable (PosFin 65) f7971 := by
  apply lratCheckerSound f7971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7971
  · intro a ha; simp [p7971] at ha; subst a; trivial
  · exact checked7971
theorem derived7971 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7971 := by
  apply localUnsat_implies_entails f7971 [c7849, c7939, c7952, c7955, c7957, c7969, c7592, c7953, c7130, c7970, c7680, c7596, c7968, c2344, c628] c7971 unsat7971 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7939 := derived7939 a h
  have h2 : Entails.eval a c7952 := derived7952 a h
  have h3 : Entails.eval a c7955 := derived7955 a h
  have h4 : Entails.eval a c7957 := derived7957 a h
  have h5 : Entails.eval a c7969 := derived7969 a h
  have h6 : Entails.eval a c7592 := derived7592 a h
  have h7 : Entails.eval a c7953 := derived7953 a h
  have h8 : Entails.eval a c7130 := derived7130 a h
  have h9 : Entails.eval a c7970 := derived7970 a h
  have h10 : Entails.eval a c7680 := derived7680 a h
  have h11 : Entails.eval a c7596 := derived7596 a h
  have h12 : Entails.eval a c7968 := derived7968 a h
  have h13 : Entails.eval a c2344 := h 2343 (by decide)
  have h14 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7972 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7972 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1174, some c490, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7972 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7972 : lratChecker f7972 p7972 = .success := by decide +kernel
theorem unsat7972 : Unsatisfiable (PosFin 65) f7972 := by
  apply lratCheckerSound f7972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7972
  · intro a ha; simp [p7972] at ha; subst a; trivial
  · exact checked7972
theorem derived7972 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7972 := by
  apply localUnsat_implies_entails f7972 [c1174, c490] c7972 unsat7972 (by rfl) a
  have h0 : Entails.eval a c1174 := h 1173 (by decide)
  have h1 : Entails.eval a c490 := h 489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7973 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7973 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c489, some c488, some c512, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7973 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7973 : lratChecker f7973 p7973 = .success := by decide +kernel
theorem unsat7973 : Unsatisfiable (PosFin 65) f7973 := by
  apply lratCheckerSound f7973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7973
  · intro a ha; simp [p7973] at ha; subst a; trivial
  · exact checked7973
theorem derived7973 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7973 := by
  apply localUnsat_implies_entails f7973 [c489, c488, c512] c7973 unsat7973 (by rfl) a
  have h0 : Entails.eval a c489 := h 488 (by decide)
  have h1 : Entails.eval a c488 := h 487 (by decide)
  have h2 : Entails.eval a c512 := h 511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7974 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7974 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7972, some c7973, some c1177, some c1187, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7974 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7974 : lratChecker f7974 p7974 = .success := by decide +kernel
theorem unsat7974 : Unsatisfiable (PosFin 65) f7974 := by
  apply lratCheckerSound f7974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7974
  · intro a ha; simp [p7974] at ha; subst a; trivial
  · exact checked7974
theorem derived7974 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7974 := by
  apply localUnsat_implies_entails f7974 [c7972, c7973, c1177, c1187] c7974 unsat7974 (by rfl) a
  have h0 : Entails.eval a c7972 := derived7972 a h
  have h1 : Entails.eval a c7973 := derived7973 a h
  have h2 : Entails.eval a c1177 := h 1176 (by decide)
  have h3 : Entails.eval a c1187 := h 1186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7975 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7975 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7891, some c7853, some c7974, some c2295, some c2288, some c2305, some c7881, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7975 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7975 : lratChecker f7975 p7975 = .success := by decide +kernel
theorem unsat7975 : Unsatisfiable (PosFin 65) f7975 := by
  apply lratCheckerSound f7975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7975
  · intro a ha; simp [p7975] at ha; subst a; trivial
  · exact checked7975
theorem derived7975 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7975 := by
  apply localUnsat_implies_entails f7975 [c7891, c7853, c7974, c2295, c2288, c2305, c7881] c7975 unsat7975 (by rfl) a
  have h0 : Entails.eval a c7891 := derived7891 a h
  have h1 : Entails.eval a c7853 := derived7853 a h
  have h2 : Entails.eval a c7974 := derived7974 a h
  have h3 : Entails.eval a c2295 := h 2294 (by decide)
  have h4 : Entails.eval a c2288 := h 2287 (by decide)
  have h5 : Entails.eval a c2305 := h 2304 (by decide)
  have h6 : Entails.eval a c7881 := derived7881 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7976 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7976 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7973, some c505, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7976 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7976 : lratChecker f7976 p7976 = .success := by decide +kernel
theorem unsat7976 : Unsatisfiable (PosFin 65) f7976 := by
  apply lratCheckerSound f7976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7976
  · intro a ha; simp [p7976] at ha; subst a; trivial
  · exact checked7976
theorem derived7976 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7976 := by
  apply localUnsat_implies_entails f7976 [c7973, c505] c7976 unsat7976 (by rfl) a
  have h0 : Entails.eval a c7973 := derived7973 a h
  have h1 : Entails.eval a c505 := h 504 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7977 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7977 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1095, some c940, some c1762, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7977 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7977 : lratChecker f7977 p7977 = .success := by decide +kernel
theorem unsat7977 : Unsatisfiable (PosFin 65) f7977 := by
  apply lratCheckerSound f7977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7977
  · intro a ha; simp [p7977] at ha; subst a; trivial
  · exact checked7977
theorem derived7977 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7977 := by
  apply localUnsat_implies_entails f7977 [c1095, c940, c1762] c7977 unsat7977 (by rfl) a
  have h0 : Entails.eval a c1095 := h 1094 (by decide)
  have h1 : Entails.eval a c940 := h 939 (by decide)
  have h2 : Entails.eval a c1762 := h 1761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7978 : DefaultClause 65 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7978 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7907, some c7977, some c7914, some c1526, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7978 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7978 : lratChecker f7978 p7978 = .success := by decide +kernel
theorem unsat7978 : Unsatisfiable (PosFin 65) f7978 := by
  apply lratCheckerSound f7978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7978
  · intro a ha; simp [p7978] at ha; subst a; trivial
  · exact checked7978
theorem derived7978 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7978 := by
  apply localUnsat_implies_entails f7978 [c7907, c7977, c7914, c1526] c7978 unsat7978 (by rfl) a
  have h0 : Entails.eval a c7907 := derived7907 a h
  have h1 : Entails.eval a c7977 := derived7977 a h
  have h2 : Entails.eval a c7914 := derived7914 a h
  have h3 : Entails.eval a c1526 := h 1525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7979 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7979 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1477, some c2472, some c2192, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7979 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7979 : lratChecker f7979 p7979 = .success := by decide +kernel
theorem unsat7979 : Unsatisfiable (PosFin 65) f7979 := by
  apply lratCheckerSound f7979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7979
  · intro a ha; simp [p7979] at ha; subst a; trivial
  · exact checked7979
theorem derived7979 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7979 := by
  apply localUnsat_implies_entails f7979 [c1477, c2472, c2192] c7979 unsat7979 (by rfl) a
  have h0 : Entails.eval a c1477 := h 1476 (by decide)
  have h1 : Entails.eval a c2472 := h 2471 (by decide)
  have h2 : Entails.eval a c2192 := h 2191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7980 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨13, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7980 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2190, some c589, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7980 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7980 : lratChecker f7980 p7980 = .success := by decide +kernel
theorem unsat7980 : Unsatisfiable (PosFin 65) f7980 := by
  apply lratCheckerSound f7980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7980
  · intro a ha; simp [p7980] at ha; subst a; trivial
  · exact checked7980
theorem derived7980 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7980 := by
  apply localUnsat_implies_entails f7980 [c2190, c589] c7980 unsat7980 (by rfl) a
  have h0 : Entails.eval a c2190 := h 2189 (by decide)
  have h1 : Entails.eval a c589 := h 588 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived7980

end CochromaticTwenty.Certificates.FixedCore1
