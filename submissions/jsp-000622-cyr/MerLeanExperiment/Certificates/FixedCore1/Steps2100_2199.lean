import MerLeanExperiment.Certificates.FixedCore1.Steps2000_2099

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c7981 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7981 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7976, some c7979, some c7980, some c601, some c2198, some c2206, some c2196, some c2210, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7981 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked7981 : lratChecker f7981 p7981 = .success := by decide +kernel
theorem unsat7981 : Unsatisfiable (PosFin 65) f7981 := by
  apply lratCheckerSound f7981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7981
  · intro a ha; simp [p7981] at ha; subst a; trivial
  · exact checked7981
theorem derived7981 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7981 := by
  apply localUnsat_implies_entails f7981 [c7976, c7979, c7980, c601, c2198, c2206, c2196, c2210] c7981 unsat7981 (by rfl) a
  have h0 : Entails.eval a c7976 := derived7976 a h
  have h1 : Entails.eval a c7979 := derived7979 a h
  have h2 : Entails.eval a c7980 := derived7980 a h
  have h3 : Entails.eval a c601 := h 600 (by decide)
  have h4 : Entails.eval a c2198 := h 2197 (by decide)
  have h5 : Entails.eval a c2206 := h 2205 (by decide)
  have h6 : Entails.eval a c2196 := h 2195 (by decide)
  have h7 : Entails.eval a c2210 := h 2209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7982 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7982 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c490, some c513, some c511, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7982 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7982 : lratChecker f7982 p7982 = .success := by decide +kernel
theorem unsat7982 : Unsatisfiable (PosFin 65) f7982 := by
  apply lratCheckerSound f7982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7982
  · intro a ha; simp [p7982] at ha; subst a; trivial
  · exact checked7982
theorem derived7982 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7982 := by
  apply localUnsat_implies_entails f7982 [c490, c513, c511] c7982 unsat7982 (by rfl) a
  have h0 : Entails.eval a c490 := h 489 (by decide)
  have h1 : Entails.eval a c513 := h 512 (by decide)
  have h2 : Entails.eval a c511 := h 510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7983 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7983 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7975, some c7978, some c7981, some c7926, some c7908, some c7982, some c7910, some c1049, some c601, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7983 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7983 : lratChecker f7983 p7983 = .success := by decide +kernel
theorem unsat7983 : Unsatisfiable (PosFin 65) f7983 := by
  apply lratCheckerSound f7983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7983
  · intro a ha; simp [p7983] at ha; subst a; trivial
  · exact checked7983
theorem derived7983 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7983 := by
  apply localUnsat_implies_entails f7983 [c7975, c7978, c7981, c7926, c7908, c7982, c7910, c1049, c601] c7983 unsat7983 (by rfl) a
  have h0 : Entails.eval a c7975 := derived7975 a h
  have h1 : Entails.eval a c7978 := derived7978 a h
  have h2 : Entails.eval a c7981 := derived7981 a h
  have h3 : Entails.eval a c7926 := derived7926 a h
  have h4 : Entails.eval a c7908 := derived7908 a h
  have h5 : Entails.eval a c7982 := derived7982 a h
  have h6 : Entails.eval a c7910 := derived7910 a h
  have h7 : Entails.eval a c1049 := h 1048 (by decide)
  have h8 : Entails.eval a c601 := h 600 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7984 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7984 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7570, some c7892, some c7893, some c1528, some c1488, some c855, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7984 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7984 : lratChecker f7984 p7984 = .success := by decide +kernel
theorem unsat7984 : Unsatisfiable (PosFin 65) f7984 := by
  apply lratCheckerSound f7984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7984
  · intro a ha; simp [p7984] at ha; subst a; trivial
  · exact checked7984
theorem derived7984 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7984 := by
  apply localUnsat_implies_entails f7984 [c7570, c7892, c7893, c1528, c1488, c855] c7984 unsat7984 (by rfl) a
  have h0 : Entails.eval a c7570 := derived7570 a h
  have h1 : Entails.eval a c7892 := derived7892 a h
  have h2 : Entails.eval a c7893 := derived7893 a h
  have h3 : Entails.eval a c1528 := h 1527 (by decide)
  have h4 : Entails.eval a c1488 := h 1487 (by decide)
  have h5 : Entails.eval a c855 := h 854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7985 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7985 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c1477, some c1000, some c425, some c150, some c156, some c2978, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7985 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7985 : lratChecker f7985 p7985 = .success := by decide +kernel
theorem unsat7985 : Unsatisfiable (PosFin 65) f7985 := by
  apply lratCheckerSound f7985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7985
  · intro a ha; simp [p7985] at ha; subst a; trivial
  · exact checked7985
theorem derived7985 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7985 := by
  apply localUnsat_implies_entails f7985 [c7849, c1477, c1000, c425, c150, c156, c2978] c7985 unsat7985 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c1477 := h 1476 (by decide)
  have h2 : Entails.eval a c1000 := h 999 (by decide)
  have h3 : Entails.eval a c425 := h 424 (by decide)
  have h4 : Entails.eval a c150 := h 149 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c2978 := h 2977 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7986 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7986 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1003, some c1386, some c654, some c564, some c7574, some c2494, some c2485, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7986 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7986 : lratChecker f7986 p7986 = .success := by decide +kernel
theorem unsat7986 : Unsatisfiable (PosFin 65) f7986 := by
  apply lratCheckerSound f7986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7986
  · intro a ha; simp [p7986] at ha; subst a; trivial
  · exact checked7986
theorem derived7986 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7986 := by
  apply localUnsat_implies_entails f7986 [c1003, c1386, c654, c564, c7574, c2494, c2485] c7986 unsat7986 (by rfl) a
  have h0 : Entails.eval a c1003 := h 1002 (by decide)
  have h1 : Entails.eval a c1386 := h 1385 (by decide)
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c564 := h 563 (by decide)
  have h4 : Entails.eval a c7574 := derived7574 a h
  have h5 : Entails.eval a c2494 := h 2493 (by decide)
  have h6 : Entails.eval a c2485 := h 2484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7987 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7987 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7971, some c7941, some c7983, some c7984, some c7981, some c7570, some c7985, some c7986, some c1526, some c1027, some c540, some c519, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7987 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7987 : lratChecker f7987 p7987 = .success := by decide +kernel
theorem unsat7987 : Unsatisfiable (PosFin 65) f7987 := by
  apply lratCheckerSound f7987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7987
  · intro a ha; simp [p7987] at ha; subst a; trivial
  · exact checked7987
theorem derived7987 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7987 := by
  apply localUnsat_implies_entails f7987 [c7849, c7971, c7941, c7983, c7984, c7981, c7570, c7985, c7986, c1526, c1027, c540, c519] c7987 unsat7987 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7971 := derived7971 a h
  have h2 : Entails.eval a c7941 := derived7941 a h
  have h3 : Entails.eval a c7983 := derived7983 a h
  have h4 : Entails.eval a c7984 := derived7984 a h
  have h5 : Entails.eval a c7981 := derived7981 a h
  have h6 : Entails.eval a c7570 := derived7570 a h
  have h7 : Entails.eval a c7985 := derived7985 a h
  have h8 : Entails.eval a c7986 := derived7986 a h
  have h9 : Entails.eval a c1526 := h 1525 (by decide)
  have h10 : Entails.eval a c1027 := h 1026 (by decide)
  have h11 : Entails.eval a c540 := h 539 (by decide)
  have h12 : Entails.eval a c519 := h 518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7988 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨7, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7988 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2463, some c1158, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7988 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7988 : lratChecker f7988 p7988 = .success := by decide +kernel
theorem unsat7988 : Unsatisfiable (PosFin 65) f7988 := by
  apply lratCheckerSound f7988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7988
  · intro a ha; simp [p7988] at ha; subst a; trivial
  · exact checked7988
theorem derived7988 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7988 := by
  apply localUnsat_implies_entails f7988 [c2463, c1158] c7988 unsat7988 (by rfl) a
  have h0 : Entails.eval a c2463 := h 2462 (by decide)
  have h1 : Entails.eval a c1158 := h 1157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7989 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7989 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1474, some c1488, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p7989 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7989 : lratChecker f7989 p7989 = .success := by decide +kernel
theorem unsat7989 : Unsatisfiable (PosFin 65) f7989 := by
  apply lratCheckerSound f7989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7989
  · intro a ha; simp [p7989] at ha; subst a; trivial
  · exact checked7989
theorem derived7989 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7989 := by
  apply localUnsat_implies_entails f7989 [c1474, c1488] c7989 unsat7989 (by rfl) a
  have h0 : Entails.eval a c1474 := h 1473 (by decide)
  have h1 : Entails.eval a c1488 := h 1487 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7990 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7990 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7570, some c7989, some c2190, some c564, some c7988, some c1388, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7990 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked7990 : lratChecker f7990 p7990 = .success := by decide +kernel
theorem unsat7990 : Unsatisfiable (PosFin 65) f7990 := by
  apply lratCheckerSound f7990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7990
  · intro a ha; simp [p7990] at ha; subst a; trivial
  · exact checked7990
theorem derived7990 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7990 := by
  apply localUnsat_implies_entails f7990 [c7570, c7989, c2190, c564, c7988, c1388] c7990 unsat7990 (by rfl) a
  have h0 : Entails.eval a c7570 := derived7570 a h
  have h1 : Entails.eval a c7989 := derived7989 a h
  have h2 : Entails.eval a c2190 := h 2189 (by decide)
  have h3 : Entails.eval a c564 := h 563 (by decide)
  have h4 : Entails.eval a c7988 := derived7988 a h
  have h5 : Entails.eval a c1388 := h 1387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7991 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7991 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7941, some c7849, some c7971, some c7983, some c7570, some c7989, some c7984, some c7987, some c7979, some c7990, some c1526, some c1235, some c1237, some c1226, some c1224, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7991 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked7991 : lratChecker f7991 p7991 = .success := by decide +kernel
theorem unsat7991 : Unsatisfiable (PosFin 65) f7991 := by
  apply lratCheckerSound f7991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7991
  · intro a ha; simp [p7991] at ha; subst a; trivial
  · exact checked7991
theorem derived7991 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7991 := by
  apply localUnsat_implies_entails f7991 [c7941, c7849, c7971, c7983, c7570, c7989, c7984, c7987, c7979, c7990, c1526, c1235, c1237, c1226, c1224] c7991 unsat7991 (by rfl) a
  have h0 : Entails.eval a c7941 := derived7941 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c7971 := derived7971 a h
  have h3 : Entails.eval a c7983 := derived7983 a h
  have h4 : Entails.eval a c7570 := derived7570 a h
  have h5 : Entails.eval a c7989 := derived7989 a h
  have h6 : Entails.eval a c7984 := derived7984 a h
  have h7 : Entails.eval a c7987 := derived7987 a h
  have h8 : Entails.eval a c7979 := derived7979 a h
  have h9 : Entails.eval a c7990 := derived7990 a h
  have h10 : Entails.eval a c1526 := h 1525 (by decide)
  have h11 : Entails.eval a c1235 := h 1234 (by decide)
  have h12 : Entails.eval a c1237 := h 1236 (by decide)
  have h13 : Entails.eval a c1226 := h 1225 (by decide)
  have h14 : Entails.eval a c1224 := h 1223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7992 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7992 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1003, some c1388, some c654, some c564, some c7574, some c2485, some c2663, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7992 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked7992 : lratChecker f7992 p7992 = .success := by decide +kernel
theorem unsat7992 : Unsatisfiable (PosFin 65) f7992 := by
  apply lratCheckerSound f7992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7992
  · intro a ha; simp [p7992] at ha; subst a; trivial
  · exact checked7992
theorem derived7992 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7992 := by
  apply localUnsat_implies_entails f7992 [c1003, c1388, c654, c564, c7574, c2485, c2663] c7992 unsat7992 (by rfl) a
  have h0 : Entails.eval a c1003 := h 1002 (by decide)
  have h1 : Entails.eval a c1388 := h 1387 (by decide)
  have h2 : Entails.eval a c654 := h 653 (by decide)
  have h3 : Entails.eval a c564 := h 563 (by decide)
  have h4 : Entails.eval a c7574 := derived7574 a h
  have h5 : Entails.eval a c2485 := h 2484 (by decide)
  have h6 : Entails.eval a c2663 := h 2662 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7993 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7993 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7991, some c7849, some c7971, some c7941, some c7983, some c7570, some c7982, some c7985, some c7992, some c1526, some c1024, some c7961, some c1025, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7993 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked7993 : lratChecker f7993 p7993 = .success := by decide +kernel
theorem unsat7993 : Unsatisfiable (PosFin 65) f7993 := by
  apply lratCheckerSound f7993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7993
  · intro a ha; simp [p7993] at ha; subst a; trivial
  · exact checked7993
theorem derived7993 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7993 := by
  apply localUnsat_implies_entails f7993 [c7991, c7849, c7971, c7941, c7983, c7570, c7982, c7985, c7992, c1526, c1024, c7961, c1025] c7993 unsat7993 (by rfl) a
  have h0 : Entails.eval a c7991 := derived7991 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c7971 := derived7971 a h
  have h3 : Entails.eval a c7941 := derived7941 a h
  have h4 : Entails.eval a c7983 := derived7983 a h
  have h5 : Entails.eval a c7570 := derived7570 a h
  have h6 : Entails.eval a c7982 := derived7982 a h
  have h7 : Entails.eval a c7985 := derived7985 a h
  have h8 : Entails.eval a c7992 := derived7992 a h
  have h9 : Entails.eval a c1526 := h 1525 (by decide)
  have h10 : Entails.eval a c1024 := h 1023 (by decide)
  have h11 : Entails.eval a c7961 := derived7961 a h
  have h12 : Entails.eval a c1025 := h 1024 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7994 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7994 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7971, some c7849, some c7941, some c7983, some c7570, some c7989, some c7991, some c7993, some c7910, some c7990, some c1526, some c1237, some c1226, some c1227, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p7994 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked7994 : lratChecker f7994 p7994 = .success := by decide +kernel
theorem unsat7994 : Unsatisfiable (PosFin 65) f7994 := by
  apply lratCheckerSound f7994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7994
  · intro a ha; simp [p7994] at ha; subst a; trivial
  · exact checked7994
theorem derived7994 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7994 := by
  apply localUnsat_implies_entails f7994 [c7971, c7849, c7941, c7983, c7570, c7989, c7991, c7993, c7910, c7990, c1526, c1237, c1226, c1227] c7994 unsat7994 (by rfl) a
  have h0 : Entails.eval a c7971 := derived7971 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c7941 := derived7941 a h
  have h3 : Entails.eval a c7983 := derived7983 a h
  have h4 : Entails.eval a c7570 := derived7570 a h
  have h5 : Entails.eval a c7989 := derived7989 a h
  have h6 : Entails.eval a c7991 := derived7991 a h
  have h7 : Entails.eval a c7993 := derived7993 a h
  have h8 : Entails.eval a c7910 := derived7910 a h
  have h9 : Entails.eval a c7990 := derived7990 a h
  have h10 : Entails.eval a c1526 := h 1525 (by decide)
  have h11 : Entails.eval a c1237 := h 1236 (by decide)
  have h12 : Entails.eval a c1226 := h 1225 (by decide)
  have h13 : Entails.eval a c1227 := h 1226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7995 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7995 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7735, some c7976, some c1176, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7995 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked7995 : lratChecker f7995 p7995 = .success := by decide +kernel
theorem unsat7995 : Unsatisfiable (PosFin 65) f7995 := by
  apply lratCheckerSound f7995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7995
  · intro a ha; simp [p7995] at ha; subst a; trivial
  · exact checked7995
theorem derived7995 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7995 := by
  apply localUnsat_implies_entails f7995 [c7735, c7976, c1176] c7995 unsat7995 (by rfl) a
  have h0 : Entails.eval a c7735 := derived7735 a h
  have h1 : Entails.eval a c7976 := derived7976 a h
  have h2 : Entails.eval a c1176 := h 1175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c7996 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7996 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7995, some c7982, some c7919, some c1192, some c1168, some c1183, some c1187, some c1514, some c516, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7996 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked7996 : lratChecker f7996 p7996 = .success := by decide +kernel
theorem unsat7996 : Unsatisfiable (PosFin 65) f7996 := by
  apply lratCheckerSound f7996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7996
  · intro a ha; simp [p7996] at ha; subst a; trivial
  · exact checked7996
theorem derived7996 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7996 := by
  apply localUnsat_implies_entails f7996 [c7995, c7982, c7919, c1192, c1168, c1183, c1187, c1514, c516] c7996 unsat7996 (by rfl) a
  have h0 : Entails.eval a c7995 := derived7995 a h
  have h1 : Entails.eval a c7982 := derived7982 a h
  have h2 : Entails.eval a c7919 := derived7919 a h
  have h3 : Entails.eval a c1192 := h 1191 (by decide)
  have h4 : Entails.eval a c1168 := h 1167 (by decide)
  have h5 : Entails.eval a c1183 := h 1182 (by decide)
  have h6 : Entails.eval a c1187 := h 1186 (by decide)
  have h7 : Entails.eval a c1514 := h 1513 (by decide)
  have h8 : Entails.eval a c516 := h 515 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c7997 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f7997 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2472, some c946, some c2409, some c1762, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p7997 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked7997 : lratChecker f7997 p7997 = .success := by decide +kernel
theorem unsat7997 : Unsatisfiable (PosFin 65) f7997 := by
  apply lratCheckerSound f7997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7997
  · intro a ha; simp [p7997] at ha; subst a; trivial
  · exact checked7997
theorem derived7997 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7997 := by
  apply localUnsat_implies_entails f7997 [c2472, c946, c2409, c1762] c7997 unsat7997 (by rfl) a
  have h0 : Entails.eval a c2472 := h 2471 (by decide)
  have h1 : Entails.eval a c946 := h 945 (by decide)
  have h2 : Entails.eval a c2409 := h 2408 (by decide)
  have h3 : Entails.eval a c1762 := h 1761 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c7998 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7998 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c635, some c641, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p7998 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7998 : lratChecker f7998 p7998 = .success := by decide +kernel
theorem unsat7998 : Unsatisfiable (PosFin 65) f7998 := by
  apply lratCheckerSound f7998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7998
  · intro a ha; simp [p7998] at ha; subst a; trivial
  · exact checked7998
theorem derived7998 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7998 := by
  apply localUnsat_implies_entails f7998 [c635, c641] c7998 unsat7998 (by rfl) a
  have h0 : Entails.eval a c635 := h 634 (by decide)
  have h1 : Entails.eval a c641 := h 640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c7999 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨13, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f7999 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c947, some c942, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p7999 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked7999 : lratChecker f7999 p7999 = .success := by decide +kernel
theorem unsat7999 : Unsatisfiable (PosFin 65) f7999 := by
  apply lratCheckerSound f7999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p7999
  · intro a ha; simp [p7999] at ha; subst a; trivial
  · exact checked7999
theorem derived7999 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c7999 := by
  apply localUnsat_implies_entails f7999 [c947, c942] c7999 unsat7999 (by rfl) a
  have h0 : Entails.eval a c947 := h 946 (by decide)
  have h1 : Entails.eval a c942 := h 941 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8000 : DefaultClause 65 := directClause [(⟨30, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8000 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2410, some c1763, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8000 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8000 : lratChecker f8000 p8000 = .success := by decide +kernel
theorem unsat8000 : Unsatisfiable (PosFin 65) f8000 := by
  apply lratCheckerSound f8000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8000
  · intro a ha; simp [p8000] at ha; subst a; trivial
  · exact checked8000
theorem derived8000 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8000 := by
  apply localUnsat_implies_entails f8000 [c2410, c1763] c8000 unsat8000 (by rfl) a
  have h0 : Entails.eval a c2410 := h 2409 (by decide)
  have h1 : Entails.eval a c1763 := h 1762 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8001 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8001 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7995, some c7923, some c7919, some c7982, some c7996, some c7997, some c7998, some c7999, some c8000, some c1526, some c7914, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8001 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8001 : lratChecker f8001 p8001 = .success := by decide +kernel
theorem unsat8001 : Unsatisfiable (PosFin 65) f8001 := by
  apply lratCheckerSound f8001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8001
  · intro a ha; simp [p8001] at ha; subst a; trivial
  · exact checked8001
theorem derived8001 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8001 := by
  apply localUnsat_implies_entails f8001 [c7995, c7923, c7919, c7982, c7996, c7997, c7998, c7999, c8000, c1526, c7914] c8001 unsat8001 (by rfl) a
  have h0 : Entails.eval a c7995 := derived7995 a h
  have h1 : Entails.eval a c7923 := derived7923 a h
  have h2 : Entails.eval a c7919 := derived7919 a h
  have h3 : Entails.eval a c7982 := derived7982 a h
  have h4 : Entails.eval a c7996 := derived7996 a h
  have h5 : Entails.eval a c7997 := derived7997 a h
  have h6 : Entails.eval a c7998 := derived7998 a h
  have h7 : Entails.eval a c7999 := derived7999 a h
  have h8 : Entails.eval a c8000 := derived8000 a h
  have h9 : Entails.eval a c1526 := h 1525 (by decide)
  have h10 : Entails.eval a c7914 := derived7914 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8002 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8002 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7735, some c2287, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8002 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8002 : lratChecker f8002 p8002 = .success := by decide +kernel
theorem unsat8002 : Unsatisfiable (PosFin 65) f8002 := by
  apply lratCheckerSound f8002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8002
  · intro a ha; simp [p8002] at ha; subst a; trivial
  · exact checked8002
theorem derived8002 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8002 := by
  apply localUnsat_implies_entails f8002 [c7735, c2287] c8002 unsat8002 (by rfl) a
  have h0 : Entails.eval a c7735 := derived7735 a h
  have h1 : Entails.eval a c2287 := h 2286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8003 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8003 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2293, some c2282, some c2307, some c2290, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8003 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8003 : lratChecker f8003 p8003 = .success := by decide +kernel
theorem unsat8003 : Unsatisfiable (PosFin 65) f8003 := by
  apply lratCheckerSound f8003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8003
  · intro a ha; simp [p8003] at ha; subst a; trivial
  · exact checked8003
theorem derived8003 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8003 := by
  apply localUnsat_implies_entails f8003 [c2293, c2282, c2307, c2290] c8003 unsat8003 (by rfl) a
  have h0 : Entails.eval a c2293 := h 2292 (by decide)
  have h1 : Entails.eval a c2282 := h 2281 (by decide)
  have h2 : Entails.eval a c2307 := h 2306 (by decide)
  have h3 : Entails.eval a c2290 := h 2289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8004 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8004 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8001, some c8002, some c7923, some c7919, some c8003, some c7979, some c7998, some c2188, some c2184, some c2200, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8004 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8004 : lratChecker f8004 p8004 = .success := by decide +kernel
theorem unsat8004 : Unsatisfiable (PosFin 65) f8004 := by
  apply lratCheckerSound f8004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8004
  · intro a ha; simp [p8004] at ha; subst a; trivial
  · exact checked8004
theorem derived8004 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8004 := by
  apply localUnsat_implies_entails f8004 [c8001, c8002, c7923, c7919, c8003, c7979, c7998, c2188, c2184, c2200] c8004 unsat8004 (by rfl) a
  have h0 : Entails.eval a c8001 := derived8001 a h
  have h1 : Entails.eval a c8002 := derived8002 a h
  have h2 : Entails.eval a c7923 := derived7923 a h
  have h3 : Entails.eval a c7919 := derived7919 a h
  have h4 : Entails.eval a c8003 := derived8003 a h
  have h5 : Entails.eval a c7979 := derived7979 a h
  have h6 : Entails.eval a c7998 := derived7998 a h
  have h7 : Entails.eval a c2188 := h 2187 (by decide)
  have h8 : Entails.eval a c2184 := h 2183 (by decide)
  have h9 : Entails.eval a c2200 := h 2199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8005 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8005 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1509, some c1022, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8005 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8005 : lratChecker f8005 p8005 = .success := by decide +kernel
theorem unsat8005 : Unsatisfiable (PosFin 65) f8005 := by
  apply lratCheckerSound f8005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8005
  · intro a ha; simp [p8005] at ha; subst a; trivial
  · exact checked8005
theorem derived8005 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8005 := by
  apply localUnsat_implies_entails f8005 [c1509, c1022] c8005 unsat8005 (by rfl) a
  have h0 : Entails.eval a c1509 := h 1508 (by decide)
  have h1 : Entails.eval a c1022 := h 1021 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8006 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8006 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c1012, some c425, some c150, some c156, some c3390, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8006 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8006 : lratChecker f8006 p8006 = .success := by decide +kernel
theorem unsat8006 : Unsatisfiable (PosFin 65) f8006 := by
  apply lratCheckerSound f8006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8006
  · intro a ha; simp [p8006] at ha; subst a; trivial
  · exact checked8006
theorem derived8006 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8006 := by
  apply localUnsat_implies_entails f8006 [c7849, c1012, c425, c150, c156, c3390] c8006 unsat8006 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c1012 := h 1011 (by decide)
  have h2 : Entails.eval a c425 := h 424 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c3390 := h 3389 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8007 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8007 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7903, some c1215, some c549, some c1227, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8007 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8007 : lratChecker f8007 p8007 = .success := by decide +kernel
theorem unsat8007 : Unsatisfiable (PosFin 65) f8007 := by
  apply lratCheckerSound f8007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8007
  · intro a ha; simp [p8007] at ha; subst a; trivial
  · exact checked8007
theorem derived8007 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8007 := by
  apply localUnsat_implies_entails f8007 [c7903, c1215, c549, c1227] c8007 unsat8007 (by rfl) a
  have h0 : Entails.eval a c7903 := derived7903 a h
  have h1 : Entails.eval a c1215 := h 1214 (by decide)
  have h2 : Entails.eval a c549 := h 548 (by decide)
  have h3 : Entails.eval a c1227 := h 1226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8008 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8008 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8004, some c8005, some c7923, some c7982, some c8006, some c8007, some c1510, some c7924, some c1013, some c451, some c641, some c2116, some c2419, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8008 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8008 : lratChecker f8008 p8008 = .success := by decide +kernel
theorem unsat8008 : Unsatisfiable (PosFin 65) f8008 := by
  apply lratCheckerSound f8008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8008
  · intro a ha; simp [p8008] at ha; subst a; trivial
  · exact checked8008
theorem derived8008 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8008 := by
  apply localUnsat_implies_entails f8008 [c7849, c8004, c8005, c7923, c7982, c8006, c8007, c1510, c7924, c1013, c451, c641, c2116, c2419] c8008 unsat8008 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8004 := derived8004 a h
  have h2 : Entails.eval a c8005 := derived8005 a h
  have h3 : Entails.eval a c7923 := derived7923 a h
  have h4 : Entails.eval a c7982 := derived7982 a h
  have h5 : Entails.eval a c8006 := derived8006 a h
  have h6 : Entails.eval a c8007 := derived8007 a h
  have h7 : Entails.eval a c1510 := h 1509 (by decide)
  have h8 : Entails.eval a c7924 := derived7924 a h
  have h9 : Entails.eval a c1013 := h 1012 (by decide)
  have h10 : Entails.eval a c451 := h 450 (by decide)
  have h11 : Entails.eval a c641 := h 640 (by decide)
  have h12 : Entails.eval a c2116 := h 2115 (by decide)
  have h13 : Entails.eval a c2419 := h 2418 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8009 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8009 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2188, some c2184, some c2200, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8009 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8009 : lratChecker f8009 p8009 = .success := by decide +kernel
theorem unsat8009 : Unsatisfiable (PosFin 65) f8009 := by
  apply lratCheckerSound f8009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8009
  · intro a ha; simp [p8009] at ha; subst a; trivial
  · exact checked8009
theorem derived8009 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8009 := by
  apply localUnsat_implies_entails f8009 [c2188, c2184, c2200] c8009 unsat8009 (by rfl) a
  have h0 : Entails.eval a c2188 := h 2187 (by decide)
  have h1 : Entails.eval a c2184 := h 2183 (by decide)
  have h2 : Entails.eval a c2200 := h 2199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8010 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8010 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7971, some c7849, some c7994, some c8008, some c8002, some c8003, some c7923, some c7979, some c8009, some c636, some c635, some c641, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8010 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8010 : lratChecker f8010 p8010 = .success := by decide +kernel
theorem unsat8010 : Unsatisfiable (PosFin 65) f8010 := by
  apply lratCheckerSound f8010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8010
  · intro a ha; simp [p8010] at ha; subst a; trivial
  · exact checked8010
theorem derived8010 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8010 := by
  apply localUnsat_implies_entails f8010 [c7971, c7849, c7994, c8008, c8002, c8003, c7923, c7979, c8009, c636, c635, c641] c8010 unsat8010 (by rfl) a
  have h0 : Entails.eval a c7971 := derived7971 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c8008 := derived8008 a h
  have h4 : Entails.eval a c8002 := derived8002 a h
  have h5 : Entails.eval a c8003 := derived8003 a h
  have h6 : Entails.eval a c7923 := derived7923 a h
  have h7 : Entails.eval a c7979 := derived7979 a h
  have h8 : Entails.eval a c8009 := derived8009 a h
  have h9 : Entails.eval a c636 := h 635 (by decide)
  have h10 : Entails.eval a c635 := h 634 (by decide)
  have h11 : Entails.eval a c641 := h 640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8011 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8011 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c899, some c906, some c907, some c7953, some c921, some c915, some c914, some c908, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8011 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8011 : lratChecker f8011 p8011 = .success := by decide +kernel
theorem unsat8011 : Unsatisfiable (PosFin 65) f8011 := by
  apply lratCheckerSound f8011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8011
  · intro a ha; simp [p8011] at ha; subst a; trivial
  · exact checked8011
theorem derived8011 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8011 := by
  apply localUnsat_implies_entails f8011 [c899, c906, c907, c7953, c921, c915, c914, c908] c8011 unsat8011 (by rfl) a
  have h0 : Entails.eval a c899 := h 898 (by decide)
  have h1 : Entails.eval a c906 := h 905 (by decide)
  have h2 : Entails.eval a c907 := h 906 (by decide)
  have h3 : Entails.eval a c7953 := derived7953 a h
  have h4 : Entails.eval a c921 := h 920 (by decide)
  have h5 : Entails.eval a c915 := h 914 (by decide)
  have h6 : Entails.eval a c914 := h 913 (by decide)
  have h7 : Entails.eval a c908 := h 907 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8012 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8012 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7617, some c7946, some c7620, some c7597, some c1905, some c1973, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8012 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8012 : lratChecker f8012 p8012 = .success := by decide +kernel
theorem unsat8012 : Unsatisfiable (PosFin 65) f8012 := by
  apply lratCheckerSound f8012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8012
  · intro a ha; simp [p8012] at ha; subst a; trivial
  · exact checked8012
theorem derived8012 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8012 := by
  apply localUnsat_implies_entails f8012 [c7617, c7946, c7620, c7597, c1905, c1973] c8012 unsat8012 (by rfl) a
  have h0 : Entails.eval a c7617 := derived7617 a h
  have h1 : Entails.eval a c7946 := derived7946 a h
  have h2 : Entails.eval a c7620 := derived7620 a h
  have h3 : Entails.eval a c7597 := derived7597 a h
  have h4 : Entails.eval a c1905 := h 1904 (by decide)
  have h5 : Entails.eval a c1973 := h 1972 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8013 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8013 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8010, some c7971, some c7849, some c7941, some c7948, some c8011, some c8012, some c2293, some c2297, some c2307, some c2290, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8013 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8013 : lratChecker f8013 p8013 = .success := by decide +kernel
theorem unsat8013 : Unsatisfiable (PosFin 65) f8013 := by
  apply lratCheckerSound f8013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8013
  · intro a ha; simp [p8013] at ha; subst a; trivial
  · exact checked8013
theorem derived8013 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8013 := by
  apply localUnsat_implies_entails f8013 [c8010, c7971, c7849, c7941, c7948, c8011, c8012, c2293, c2297, c2307, c2290] c8013 unsat8013 (by rfl) a
  have h0 : Entails.eval a c8010 := derived8010 a h
  have h1 : Entails.eval a c7971 := derived7971 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c7941 := derived7941 a h
  have h4 : Entails.eval a c7948 := derived7948 a h
  have h5 : Entails.eval a c8011 := derived8011 a h
  have h6 : Entails.eval a c8012 := derived8012 a h
  have h7 : Entails.eval a c2293 := h 2292 (by decide)
  have h8 : Entails.eval a c2297 := h 2296 (by decide)
  have h9 : Entails.eval a c2307 := h 2306 (by decide)
  have h10 : Entails.eval a c2290 := h 2289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8014 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8014 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7343, some c7765, some c7976, some c1176, some c1345, some c1280, some c7742, some c8000, some c134, some c541, some c551, some c669, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8014 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8014 : lratChecker f8014 p8014 = .success := by decide +kernel
theorem unsat8014 : Unsatisfiable (PosFin 65) f8014 := by
  apply lratCheckerSound f8014 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8014
  · intro a ha; simp [p8014] at ha; subst a; trivial
  · exact checked8014
theorem derived8014 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8014 := by
  apply localUnsat_implies_entails f8014 [c7849, c7343, c7765, c7976, c1176, c1345, c1280, c7742, c8000, c134, c541, c551, c669] c8014 unsat8014 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7343 := derived7343 a h
  have h2 : Entails.eval a c7765 := derived7765 a h
  have h3 : Entails.eval a c7976 := derived7976 a h
  have h4 : Entails.eval a c1176 := h 1175 (by decide)
  have h5 : Entails.eval a c1345 := h 1344 (by decide)
  have h6 : Entails.eval a c1280 := h 1279 (by decide)
  have h7 : Entails.eval a c7742 := derived7742 a h
  have h8 : Entails.eval a c8000 := derived8000 a h
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c541 := h 540 (by decide)
  have h11 : Entails.eval a c551 := h 550 (by decide)
  have h12 : Entails.eval a c669 := h 668 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8015 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8015 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7568, some c7895, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8015 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8015 : lratChecker f8015 p8015 = .success := by decide +kernel
theorem unsat8015 : Unsatisfiable (PosFin 65) f8015 := by
  apply lratCheckerSound f8015 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8015
  · intro a ha; simp [p8015] at ha; subst a; trivial
  · exact checked8015
theorem derived8015 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8015 := by
  apply localUnsat_implies_entails f8015 [c7568, c7895] c8015 unsat8015 (by rfl) a
  have h0 : Entails.eval a c7568 := derived7568 a h
  have h1 : Entails.eval a c7895 := derived7895 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8016 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, false), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8016 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1192, some c1187, some c7963, some c7964, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8016 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8016 : lratChecker f8016 p8016 = .success := by decide +kernel
theorem unsat8016 : Unsatisfiable (PosFin 65) f8016 := by
  apply lratCheckerSound f8016 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8016
  · intro a ha; simp [p8016] at ha; subst a; trivial
  · exact checked8016
theorem derived8016 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8016 := by
  apply localUnsat_implies_entails f8016 [c1192, c1187, c7963, c7964] c8016 unsat8016 (by rfl) a
  have h0 : Entails.eval a c1192 := h 1191 (by decide)
  have h1 : Entails.eval a c1187 := h 1186 (by decide)
  have h2 : Entails.eval a c7963 := derived7963 a h
  have h3 : Entails.eval a c7964 := derived7964 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8017 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8017 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8014, some c7982, some c7999, some c8015, some c8016, some c7419, some c7443, some c7617, some c7963, some c530, some c2162, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8017 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8017 : lratChecker f8017 p8017 = .success := by decide +kernel
theorem unsat8017 : Unsatisfiable (PosFin 65) f8017 := by
  apply lratCheckerSound f8017 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8017
  · intro a ha; simp [p8017] at ha; subst a; trivial
  · exact checked8017
theorem derived8017 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8017 := by
  apply localUnsat_implies_entails f8017 [c7849, c8014, c7982, c7999, c8015, c8016, c7419, c7443, c7617, c7963, c530, c2162] c8017 unsat8017 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8014 := derived8014 a h
  have h2 : Entails.eval a c7982 := derived7982 a h
  have h3 : Entails.eval a c7999 := derived7999 a h
  have h4 : Entails.eval a c8015 := derived8015 a h
  have h5 : Entails.eval a c8016 := derived8016 a h
  have h6 : Entails.eval a c7419 := derived7419 a h
  have h7 : Entails.eval a c7443 := derived7443 a h
  have h8 : Entails.eval a c7617 := derived7617 a h
  have h9 : Entails.eval a c7963 := derived7963 a h
  have h10 : Entails.eval a c530 := h 529 (by decide)
  have h11 : Entails.eval a c2162 := h 2161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8018 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8018 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8017, some c903, some c7953, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8018 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8018 : lratChecker f8018 p8018 = .success := by decide +kernel
theorem unsat8018 : Unsatisfiable (PosFin 65) f8018 := by
  apply lratCheckerSound f8018 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8018
  · intro a ha; simp [p8018] at ha; subst a; trivial
  · exact checked8018
theorem derived8018 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8018 := by
  apply localUnsat_implies_entails f8018 [c8017, c903, c7953] c8018 unsat8018 (by rfl) a
  have h0 : Entails.eval a c8017 := derived8017 a h
  have h1 : Entails.eval a c903 := h 902 (by decide)
  have h2 : Entails.eval a c7953 := derived7953 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8019 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8019 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2187, some c1345, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8019 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8019 : lratChecker f8019 p8019 = .success := by decide +kernel
theorem unsat8019 : Unsatisfiable (PosFin 65) f8019 := by
  apply lratCheckerSound f8019 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8019
  · intro a ha; simp [p8019] at ha; subst a; trivial
  · exact checked8019
theorem derived8019 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8019 := by
  apply localUnsat_implies_entails f8019 [c2187, c1345] c8019 unsat8019 (by rfl) a
  have h0 : Entails.eval a c2187 := h 2186 (by decide)
  have h1 : Entails.eval a c1345 := h 1344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8020 : DefaultClause 65 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, false), (⟨58, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8020 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8018, some c8003, some c7568, some c7617, some c7623, some c8019, some c8009, some c1354, some c1362, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8020 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8020 : lratChecker f8020 p8020 = .success := by decide +kernel
theorem unsat8020 : Unsatisfiable (PosFin 65) f8020 := by
  apply lratCheckerSound f8020 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8020
  · intro a ha; simp [p8020] at ha; subst a; trivial
  · exact checked8020
theorem derived8020 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8020 := by
  apply localUnsat_implies_entails f8020 [c8018, c8003, c7568, c7617, c7623, c8019, c8009, c1354, c1362] c8020 unsat8020 (by rfl) a
  have h0 : Entails.eval a c8018 := derived8018 a h
  have h1 : Entails.eval a c8003 := derived8003 a h
  have h2 : Entails.eval a c7568 := derived7568 a h
  have h3 : Entails.eval a c7617 := derived7617 a h
  have h4 : Entails.eval a c7623 := derived7623 a h
  have h5 : Entails.eval a c8019 := derived8019 a h
  have h6 : Entails.eval a c8009 := derived8009 a h
  have h7 : Entails.eval a c1354 := h 1353 (by decide)
  have h8 : Entails.eval a c1362 := h 1361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8021 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8021 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7971, some c8010, some c8013, some c8020, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8021 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8021 : lratChecker f8021 p8021 = .success := by decide +kernel
theorem unsat8021 : Unsatisfiable (PosFin 65) f8021 := by
  apply lratCheckerSound f8021 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8021
  · intro a ha; simp [p8021] at ha; subst a; trivial
  · exact checked8021
theorem derived8021 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8021 := by
  apply localUnsat_implies_entails f8021 [c7971, c8010, c8013, c8020] c8021 unsat8021 (by rfl) a
  have h0 : Entails.eval a c7971 := derived7971 a h
  have h1 : Entails.eval a c8010 := derived8010 a h
  have h2 : Entails.eval a c8013 := derived8013 a h
  have h3 : Entails.eval a c8020 := derived8020 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8022 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8022 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c7989, some c854, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8022 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8022 : lratChecker f8022 p8022 = .success := by decide +kernel
theorem unsat8022 : Unsatisfiable (PosFin 65) f8022 := by
  apply lratCheckerSound f8022 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8022
  · intro a ha; simp [p8022] at ha; subst a; trivial
  · exact checked8022
theorem derived8022 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8022 := by
  apply localUnsat_implies_entails f8022 [c545, c553, c7989, c854] c8022 unsat8022 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c7989 := derived7989 a h
  have h3 : Entails.eval a c854 := h 853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8023 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8023 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1507, some c1511, some c1525, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8023 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8023 : lratChecker f8023 p8023 = .success := by decide +kernel
theorem unsat8023 : Unsatisfiable (PosFin 65) f8023 := by
  apply lratCheckerSound f8023 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8023
  · intro a ha; simp [p8023] at ha; subst a; trivial
  · exact checked8023
theorem derived8023 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8023 := by
  apply localUnsat_implies_entails f8023 [c1507, c1511, c1525] c8023 unsat8023 (by rfl) a
  have h0 : Entails.eval a c1507 := h 1506 (by decide)
  have h1 : Entails.eval a c1511 := h 1510 (by decide)
  have h2 : Entails.eval a c1525 := h 1524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8024 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8024 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8023, some c2288, some c2285, some c1488, some c855, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8024 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8024 : lratChecker f8024 p8024 = .success := by decide +kernel
theorem unsat8024 : Unsatisfiable (PosFin 65) f8024 := by
  apply lratCheckerSound f8024 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8024
  · intro a ha; simp [p8024] at ha; subst a; trivial
  · exact checked8024
theorem derived8024 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8024 := by
  apply localUnsat_implies_entails f8024 [c8023, c2288, c2285, c1488, c855] c8024 unsat8024 (by rfl) a
  have h0 : Entails.eval a c8023 := derived8023 a h
  have h1 : Entails.eval a c2288 := h 2287 (by decide)
  have h2 : Entails.eval a c2285 := h 2284 (by decide)
  have h3 : Entails.eval a c1488 := h 1487 (by decide)
  have h4 : Entails.eval a c855 := h 854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8025 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8025 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8023, some c7989, some c2682, some c2677, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8025 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8025 : lratChecker f8025 p8025 = .success := by decide +kernel
theorem unsat8025 : Unsatisfiable (PosFin 65) f8025 := by
  apply lratCheckerSound f8025 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8025
  · intro a ha; simp [p8025] at ha; subst a; trivial
  · exact checked8025
theorem derived8025 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8025 := by
  apply localUnsat_implies_entails f8025 [c8023, c7989, c2682, c2677] c8025 unsat8025 (by rfl) a
  have h0 : Entails.eval a c8023 := derived8023 a h
  have h1 : Entails.eval a c7989 := derived7989 a h
  have h2 : Entails.eval a c2682 := h 2681 (by decide)
  have h3 : Entails.eval a c2677 := h 2676 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8026 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8026 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8022, some c8024, some c8025, some c1470, some c2675, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8026 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8026 : lratChecker f8026 p8026 = .success := by decide +kernel
theorem unsat8026 : Unsatisfiable (PosFin 65) f8026 := by
  apply lratCheckerSound f8026 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8026
  · intro a ha; simp [p8026] at ha; subst a; trivial
  · exact checked8026
theorem derived8026 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8026 := by
  apply localUnsat_implies_entails f8026 [c8022, c8024, c8025, c1470, c2675] c8026 unsat8026 (by rfl) a
  have h0 : Entails.eval a c8022 := derived8022 a h
  have h1 : Entails.eval a c8024 := derived8024 a h
  have h2 : Entails.eval a c8025 := derived8025 a h
  have h3 : Entails.eval a c1470 := h 1469 (by decide)
  have h4 : Entails.eval a c2675 := h 2674 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8027 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8027 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8023, some c8026, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8027 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8027 : lratChecker f8027 p8027 = .success := by decide +kernel
theorem unsat8027 : Unsatisfiable (PosFin 65) f8027 := by
  apply lratCheckerSound f8027 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8027
  · intro a ha; simp [p8027] at ha; subst a; trivial
  · exact checked8027
theorem derived8027 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8027 := by
  apply localUnsat_implies_entails f8027 [c8023, c8026] c8027 unsat8027 (by rfl) a
  have h0 : Entails.eval a c8023 := derived8023 a h
  have h1 : Entails.eval a c8026 := derived8026 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8028 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8028 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c522, some c1333, some c2154, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8028 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8028 : lratChecker f8028 p8028 = .success := by decide +kernel
theorem unsat8028 : Unsatisfiable (PosFin 65) f8028 := by
  apply lratCheckerSound f8028 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8028
  · intro a ha; simp [p8028] at ha; subst a; trivial
  · exact checked8028
theorem derived8028 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8028 := by
  apply localUnsat_implies_entails f8028 [c522, c1333, c2154] c8028 unsat8028 (by rfl) a
  have h0 : Entails.eval a c522 := h 521 (by decide)
  have h1 : Entails.eval a c1333 := h 1332 (by decide)
  have h2 : Entails.eval a c2154 := h 2153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8029 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨28, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, false), (⟨30, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8029 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c1090, some c855, some c140, some c6687, some c3350, some c1029, some c73, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8029 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8029 : lratChecker f8029 p8029 = .success := by decide +kernel
theorem unsat8029 : Unsatisfiable (PosFin 65) f8029 := by
  apply lratCheckerSound f8029 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8029
  · intro a ha; simp [p8029] at ha; subst a; trivial
  · exact checked8029
theorem derived8029 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8029 := by
  apply localUnsat_implies_entails f8029 [c7849, c1090, c855, c140, c6687, c3350, c1029, c73] c8029 unsat8029 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c1090 := h 1089 (by decide)
  have h2 : Entails.eval a c855 := h 854 (by decide)
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c6687 := derived6687 a h
  have h5 : Entails.eval a c3350 := h 3349 (by decide)
  have h6 : Entails.eval a c1029 := h 1028 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8030 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8030 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2009, some c2171, some c1377, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p8030 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8030 : lratChecker f8030 p8030 = .success := by decide +kernel
theorem unsat8030 : Unsatisfiable (PosFin 65) f8030 := by
  apply lratCheckerSound f8030 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8030
  · intro a ha; simp [p8030] at ha; subst a; trivial
  · exact checked8030
theorem derived8030 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8030 := by
  apply localUnsat_implies_entails f8030 [c2009, c2171, c1377] c8030 unsat8030 (by rfl) a
  have h0 : Entails.eval a c2009 := h 2008 (by decide)
  have h1 : Entails.eval a c2171 := h 2170 (by decide)
  have h2 : Entails.eval a c1377 := h 1376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8031 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8031 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7941, some c8021, some c8027, some c7948, some c899, some c906, some c907, some c901, some c931, some c877, some c914, some c921, some c911, some c8028, some c8030, some c855, some c8029, some c2588, some c7620, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8031 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked8031 : lratChecker f8031 p8031 = .success := by decide +kernel
theorem unsat8031 : Unsatisfiable (PosFin 65) f8031 := by
  apply lratCheckerSound f8031 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8031
  · intro a ha; simp [p8031] at ha; subst a; trivial
  · exact checked8031
theorem derived8031 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8031 := by
  apply localUnsat_implies_entails f8031 [c7849, c7941, c8021, c8027, c7948, c899, c906, c907, c901, c931, c877, c914, c921, c911, c8028, c8030, c855, c8029, c2588, c7620] c8031 unsat8031 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7941 := derived7941 a h
  have h2 : Entails.eval a c8021 := derived8021 a h
  have h3 : Entails.eval a c8027 := derived8027 a h
  have h4 : Entails.eval a c7948 := derived7948 a h
  have h5 : Entails.eval a c899 := h 898 (by decide)
  have h6 : Entails.eval a c906 := h 905 (by decide)
  have h7 : Entails.eval a c907 := h 906 (by decide)
  have h8 : Entails.eval a c901 := h 900 (by decide)
  have h9 : Entails.eval a c931 := h 930 (by decide)
  have h10 : Entails.eval a c877 := h 876 (by decide)
  have h11 : Entails.eval a c914 := h 913 (by decide)
  have h12 : Entails.eval a c921 := h 920 (by decide)
  have h13 : Entails.eval a c911 := h 910 (by decide)
  have h14 : Entails.eval a c8028 := derived8028 a h
  have h15 : Entails.eval a c8030 := derived8030 a h
  have h16 : Entails.eval a c855 := h 854 (by decide)
  have h17 : Entails.eval a c8029 := derived8029 a h
  have h18 : Entails.eval a c2588 := h 2587 (by decide)
  have h19 : Entails.eval a c7620 := derived7620 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8032 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8032 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2286, some c2289, some c2288, some c2285, some c7954, some c2298, some c884, some c2290, some c8030, some c1234, some c1089, some c2226, some c2551, some c1562, some c2355, some c2347, some c6711, some c2405, some c83, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8032 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8032 : lratChecker f8032 p8032 = .success := by decide +kernel
theorem unsat8032 : Unsatisfiable (PosFin 65) f8032 := by
  apply lratCheckerSound f8032 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8032
  · intro a ha; simp [p8032] at ha; subst a; trivial
  · exact checked8032
theorem derived8032 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8032 := by
  apply localUnsat_implies_entails f8032 [c2286, c2289, c2288, c2285, c7954, c2298, c884, c2290, c8030, c1234, c1089, c2226, c2551, c1562, c2355, c2347, c6711, c2405, c83] c8032 unsat8032 (by rfl) a
  have h0 : Entails.eval a c2286 := h 2285 (by decide)
  have h1 : Entails.eval a c2289 := h 2288 (by decide)
  have h2 : Entails.eval a c2288 := h 2287 (by decide)
  have h3 : Entails.eval a c2285 := h 2284 (by decide)
  have h4 : Entails.eval a c7954 := derived7954 a h
  have h5 : Entails.eval a c2298 := h 2297 (by decide)
  have h6 : Entails.eval a c884 := h 883 (by decide)
  have h7 : Entails.eval a c2290 := h 2289 (by decide)
  have h8 : Entails.eval a c8030 := derived8030 a h
  have h9 : Entails.eval a c1234 := h 1233 (by decide)
  have h10 : Entails.eval a c1089 := h 1088 (by decide)
  have h11 : Entails.eval a c2226 := h 2225 (by decide)
  have h12 : Entails.eval a c2551 := h 2550 (by decide)
  have h13 : Entails.eval a c1562 := h 1561 (by decide)
  have h14 : Entails.eval a c2355 := h 2354 (by decide)
  have h15 : Entails.eval a c2347 := h 2346 (by decide)
  have h16 : Entails.eval a c6711 := derived6711 a h
  have h17 : Entails.eval a c2405 := h 2404 (by decide)
  have h18 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8033 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8033 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8021, some c7849, some c7941, some c8027, some c7948, some c8031, some c8032, some c7946, some c7586, some c8012, some c7581, some c7597, some c7951, some c1904, some c2190, some c2199, some c2200, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8033 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8033 : lratChecker f8033 p8033 = .success := by decide +kernel
theorem unsat8033 : Unsatisfiable (PosFin 65) f8033 := by
  apply lratCheckerSound f8033 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8033
  · intro a ha; simp [p8033] at ha; subst a; trivial
  · exact checked8033
theorem derived8033 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8033 := by
  apply localUnsat_implies_entails f8033 [c8021, c7849, c7941, c8027, c7948, c8031, c8032, c7946, c7586, c8012, c7581, c7597, c7951, c1904, c2190, c2199, c2200] c8033 unsat8033 (by rfl) a
  have h0 : Entails.eval a c8021 := derived8021 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c7941 := derived7941 a h
  have h3 : Entails.eval a c8027 := derived8027 a h
  have h4 : Entails.eval a c7948 := derived7948 a h
  have h5 : Entails.eval a c8031 := derived8031 a h
  have h6 : Entails.eval a c8032 := derived8032 a h
  have h7 : Entails.eval a c7946 := derived7946 a h
  have h8 : Entails.eval a c7586 := derived7586 a h
  have h9 : Entails.eval a c8012 := derived8012 a h
  have h10 : Entails.eval a c7581 := derived7581 a h
  have h11 : Entails.eval a c7597 := derived7597 a h
  have h12 : Entails.eval a c7951 := derived7951 a h
  have h13 : Entails.eval a c1904 := h 1903 (by decide)
  have h14 : Entails.eval a c2190 := h 2189 (by decide)
  have h15 : Entails.eval a c2199 := h 2198 (by decide)
  have h16 : Entails.eval a c2200 := h 2199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8034 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8034 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1491, some c1527, some c858, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8034 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8034 : lratChecker f8034 p8034 = .success := by decide +kernel
theorem unsat8034 : Unsatisfiable (PosFin 65) f8034 := by
  apply lratCheckerSound f8034 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8034
  · intro a ha; simp [p8034] at ha; subst a; trivial
  · exact checked8034
theorem derived8034 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8034 := by
  apply localUnsat_implies_entails f8034 [c1491, c1527, c858] c8034 unsat8034 (by rfl) a
  have h0 : Entails.eval a c1491 := h 1490 (by decide)
  have h1 : Entails.eval a c1527 := h 1526 (by decide)
  have h2 : Entails.eval a c858 := h 857 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8035 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8035 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1466, some c1502, some c860, some c840, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8035 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8035 : lratChecker f8035 p8035 = .success := by decide +kernel
theorem unsat8035 : Unsatisfiable (PosFin 65) f8035 := by
  apply lratCheckerSound f8035 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8035
  · intro a ha; simp [p8035] at ha; subst a; trivial
  · exact checked8035
theorem derived8035 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8035 := by
  apply localUnsat_implies_entails f8035 [c1466, c1502, c860, c840] c8035 unsat8035 (by rfl) a
  have h0 : Entails.eval a c1466 := h 1465 (by decide)
  have h1 : Entails.eval a c1502 := h 1501 (by decide)
  have h2 : Entails.eval a c860 := h 859 (by decide)
  have h3 : Entails.eval a c840 := h 839 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8036 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8036 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c854, some c682, some c1401, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8036 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8036 : lratChecker f8036 p8036 = .success := by decide +kernel
theorem unsat8036 : Unsatisfiable (PosFin 65) f8036 := by
  apply lratCheckerSound f8036 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8036
  · intro a ha; simp [p8036] at ha; subst a; trivial
  · exact checked8036
theorem derived8036 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8036 := by
  apply localUnsat_implies_entails f8036 [c545, c553, c854, c682, c1401] c8036 unsat8036 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c854 := h 853 (by decide)
  have h3 : Entails.eval a c682 := h 681 (by decide)
  have h4 : Entails.eval a c1401 := h 1400 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8037 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8037 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8035, some c1501, some c1503, some c1521, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8037 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8037 : lratChecker f8037 p8037 = .success := by decide +kernel
theorem unsat8037 : Unsatisfiable (PosFin 65) f8037 := by
  apply lratCheckerSound f8037 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8037
  · intro a ha; simp [p8037] at ha; subst a; trivial
  · exact checked8037
theorem derived8037 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8037 := by
  apply localUnsat_implies_entails f8037 [c8035, c1501, c1503, c1521] c8037 unsat8037 (by rfl) a
  have h0 : Entails.eval a c8035 := derived8035 a h
  have h1 : Entails.eval a c1501 := h 1500 (by decide)
  have h2 : Entails.eval a c1503 := h 1502 (by decide)
  have h3 : Entails.eval a c1521 := h 1520 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8038 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8038 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8034, some c8036, some c1529, some c8037, some c1517, some c1526, some c1477, some c490, some c425, some c2155, some c2168, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8038 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8038 : lratChecker f8038 p8038 = .success := by decide +kernel
theorem unsat8038 : Unsatisfiable (PosFin 65) f8038 := by
  apply lratCheckerSound f8038 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8038
  · intro a ha; simp [p8038] at ha; subst a; trivial
  · exact checked8038
theorem derived8038 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8038 := by
  apply localUnsat_implies_entails f8038 [c8034, c8036, c1529, c8037, c1517, c1526, c1477, c490, c425, c2155, c2168] c8038 unsat8038 (by rfl) a
  have h0 : Entails.eval a c8034 := derived8034 a h
  have h1 : Entails.eval a c8036 := derived8036 a h
  have h2 : Entails.eval a c1529 := h 1528 (by decide)
  have h3 : Entails.eval a c8037 := derived8037 a h
  have h4 : Entails.eval a c1517 := h 1516 (by decide)
  have h5 : Entails.eval a c1526 := h 1525 (by decide)
  have h6 : Entails.eval a c1477 := h 1476 (by decide)
  have h7 : Entails.eval a c490 := h 489 (by decide)
  have h8 : Entails.eval a c425 := h 424 (by decide)
  have h9 : Entails.eval a c2155 := h 2154 (by decide)
  have h10 : Entails.eval a c2168 := h 2167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8039 : DefaultClause 65 := directClause [(⟨14, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8039 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1467, some c1496, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8039 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8039 : lratChecker f8039 p8039 = .success := by decide +kernel
theorem unsat8039 : Unsatisfiable (PosFin 65) f8039 := by
  apply lratCheckerSound f8039 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8039
  · intro a ha; simp [p8039] at ha; subst a; trivial
  · exact checked8039
theorem derived8039 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8039 := by
  apply localUnsat_implies_entails f8039 [c1467, c1496] c8039 unsat8039 (by rfl) a
  have h0 : Entails.eval a c1467 := h 1466 (by decide)
  have h1 : Entails.eval a c1496 := h 1495 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8040 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8040 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8034, some c8035, some c8037, some c8039, some c860, some c862, some c854, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8040 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8040 : lratChecker f8040 p8040 = .success := by decide +kernel
theorem unsat8040 : Unsatisfiable (PosFin 65) f8040 := by
  apply lratCheckerSound f8040 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8040
  · intro a ha; simp [p8040] at ha; subst a; trivial
  · exact checked8040
theorem derived8040 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8040 := by
  apply localUnsat_implies_entails f8040 [c8034, c8035, c8037, c8039, c860, c862, c854] c8040 unsat8040 (by rfl) a
  have h0 : Entails.eval a c8034 := derived8034 a h
  have h1 : Entails.eval a c8035 := derived8035 a h
  have h2 : Entails.eval a c8037 := derived8037 a h
  have h3 : Entails.eval a c8039 := derived8039 a h
  have h4 : Entails.eval a c860 := h 859 (by decide)
  have h5 : Entails.eval a c862 := h 861 (by decide)
  have h6 : Entails.eval a c854 := h 853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8041 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8041 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2309, some c2294, some c2293, some c2306, some c2298, some c2290, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8041 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8041 : lratChecker f8041 p8041 = .success := by decide +kernel
theorem unsat8041 : Unsatisfiable (PosFin 65) f8041 := by
  apply lratCheckerSound f8041 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8041
  · intro a ha; simp [p8041] at ha; subst a; trivial
  · exact checked8041
theorem derived8041 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8041 := by
  apply localUnsat_implies_entails f8041 [c2309, c2294, c2293, c2306, c2298, c2290] c8041 unsat8041 (by rfl) a
  have h0 : Entails.eval a c2309 := h 2308 (by decide)
  have h1 : Entails.eval a c2294 := h 2293 (by decide)
  have h2 : Entails.eval a c2293 := h 2292 (by decide)
  have h3 : Entails.eval a c2306 := h 2305 (by decide)
  have h4 : Entails.eval a c2298 := h 2297 (by decide)
  have h5 : Entails.eval a c2290 := h 2289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8042 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8042 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c860, some c842, some c859, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8042 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8042 : lratChecker f8042 p8042 = .success := by decide +kernel
theorem unsat8042 : Unsatisfiable (PosFin 65) f8042 := by
  apply lratCheckerSound f8042 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8042
  · intro a ha; simp [p8042] at ha; subst a; trivial
  · exact checked8042
theorem derived8042 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8042 := by
  apply localUnsat_implies_entails f8042 [c860, c842, c859] c8042 unsat8042 (by rfl) a
  have h0 : Entails.eval a c860 := h 859 (by decide)
  have h1 : Entails.eval a c842 := h 841 (by decide)
  have h2 : Entails.eval a c859 := h 858 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8043 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8043 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8040, some c8038, some c8034, some c8041, some c7979, some c8042, some c1484, some c2321, some c1489, some c2315, some c2334, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8043 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8043 : lratChecker f8043 p8043 = .success := by decide +kernel
theorem unsat8043 : Unsatisfiable (PosFin 65) f8043 := by
  apply lratCheckerSound f8043 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8043
  · intro a ha; simp [p8043] at ha; subst a; trivial
  · exact checked8043
theorem derived8043 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8043 := by
  apply localUnsat_implies_entails f8043 [c8040, c8038, c8034, c8041, c7979, c8042, c1484, c2321, c1489, c2315, c2334] c8043 unsat8043 (by rfl) a
  have h0 : Entails.eval a c8040 := derived8040 a h
  have h1 : Entails.eval a c8038 := derived8038 a h
  have h2 : Entails.eval a c8034 := derived8034 a h
  have h3 : Entails.eval a c8041 := derived8041 a h
  have h4 : Entails.eval a c7979 := derived7979 a h
  have h5 : Entails.eval a c8042 := derived8042 a h
  have h6 : Entails.eval a c1484 := h 1483 (by decide)
  have h7 : Entails.eval a c2321 := h 2320 (by decide)
  have h8 : Entails.eval a c1489 := h 1488 (by decide)
  have h9 : Entails.eval a c2315 := h 2314 (by decide)
  have h10 : Entails.eval a c2334 := h 2333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8044 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8044 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c860, some c842, some c854, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8044 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8044 : lratChecker f8044 p8044 = .success := by decide +kernel
theorem unsat8044 : Unsatisfiable (PosFin 65) f8044 := by
  apply lratCheckerSound f8044 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8044
  · intro a ha; simp [p8044] at ha; subst a; trivial
  · exact checked8044
theorem derived8044 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8044 := by
  apply localUnsat_implies_entails f8044 [c860, c842, c854] c8044 unsat8044 (by rfl) a
  have h0 : Entails.eval a c860 := h 859 (by decide)
  have h1 : Entails.eval a c842 := h 841 (by decide)
  have h2 : Entails.eval a c854 := h 853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8045 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8045 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8040, some c8034, some c8043, some c8044, some c1495, some c1496, some c1489, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8045 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8045 : lratChecker f8045 p8045 = .success := by decide +kernel
theorem unsat8045 : Unsatisfiable (PosFin 65) f8045 := by
  apply lratCheckerSound f8045 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8045
  · intro a ha; simp [p8045] at ha; subst a; trivial
  · exact checked8045
theorem derived8045 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8045 := by
  apply localUnsat_implies_entails f8045 [c8040, c8034, c8043, c8044, c1495, c1496, c1489] c8045 unsat8045 (by rfl) a
  have h0 : Entails.eval a c8040 := derived8040 a h
  have h1 : Entails.eval a c8034 := derived8034 a h
  have h2 : Entails.eval a c8043 := derived8043 a h
  have h3 : Entails.eval a c8044 := derived8044 a h
  have h4 : Entails.eval a c1495 := h 1494 (by decide)
  have h5 : Entails.eval a c1496 := h 1495 (by decide)
  have h6 : Entails.eval a c1489 := h 1488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8046 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8046 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8034, some c8038, some c8040, some c8045, some c1517, some c1526, some c2293, some c1477, some c2472, some c2192, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8046 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8046 : lratChecker f8046 p8046 = .success := by decide +kernel
theorem unsat8046 : Unsatisfiable (PosFin 65) f8046 := by
  apply lratCheckerSound f8046 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8046
  · intro a ha; simp [p8046] at ha; subst a; trivial
  · exact checked8046
theorem derived8046 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8046 := by
  apply localUnsat_implies_entails f8046 [c8034, c8038, c8040, c8045, c1517, c1526, c2293, c1477, c2472, c2192] c8046 unsat8046 (by rfl) a
  have h0 : Entails.eval a c8034 := derived8034 a h
  have h1 : Entails.eval a c8038 := derived8038 a h
  have h2 : Entails.eval a c8040 := derived8040 a h
  have h3 : Entails.eval a c8045 := derived8045 a h
  have h4 : Entails.eval a c1517 := h 1516 (by decide)
  have h5 : Entails.eval a c1526 := h 1525 (by decide)
  have h6 : Entails.eval a c2293 := h 2292 (by decide)
  have h7 : Entails.eval a c1477 := h 1476 (by decide)
  have h8 : Entails.eval a c2472 := h 2471 (by decide)
  have h9 : Entails.eval a c2192 := h 2191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8047 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8047 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8021, some c8033, some c8046, some c685, some c858, some c2589, some c1443, some c7504, some c1461, some c2550, some c1212, some c596, some c872, some c139, some c7130, some c3343, some c6767, some c2267, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8047 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8047 : lratChecker f8047 p8047 = .success := by decide +kernel
theorem unsat8047 : Unsatisfiable (PosFin 65) f8047 := by
  apply lratCheckerSound f8047 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8047
  · intro a ha; simp [p8047] at ha; subst a; trivial
  · exact checked8047
theorem derived8047 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8047 := by
  apply localUnsat_implies_entails f8047 [c7849, c8021, c8033, c8046, c685, c858, c2589, c1443, c7504, c1461, c2550, c1212, c596, c872, c139, c7130, c3343, c6767, c2267] c8047 unsat8047 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8021 := derived8021 a h
  have h2 : Entails.eval a c8033 := derived8033 a h
  have h3 : Entails.eval a c8046 := derived8046 a h
  have h4 : Entails.eval a c685 := h 684 (by decide)
  have h5 : Entails.eval a c858 := h 857 (by decide)
  have h6 : Entails.eval a c2589 := h 2588 (by decide)
  have h7 : Entails.eval a c1443 := h 1442 (by decide)
  have h8 : Entails.eval a c7504 := derived7504 a h
  have h9 : Entails.eval a c1461 := h 1460 (by decide)
  have h10 : Entails.eval a c2550 := h 2549 (by decide)
  have h11 : Entails.eval a c1212 := h 1211 (by decide)
  have h12 : Entails.eval a c596 := h 595 (by decide)
  have h13 : Entails.eval a c872 := h 871 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c7130 := derived7130 a h
  have h16 : Entails.eval a c3343 := h 3342 (by decide)
  have h17 : Entails.eval a c6767 := derived6767 a h
  have h18 : Entails.eval a c2267 := h 2266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8048 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8048 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8021, some c8033, some c8046, some c8047, some c2446, some c1365, some c638, some c576, some c2589, some c7504, some c2550, some c1376, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8048 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8048 : lratChecker f8048 p8048 = .success := by decide +kernel
theorem unsat8048 : Unsatisfiable (PosFin 65) f8048 := by
  apply lratCheckerSound f8048 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8048
  · intro a ha; simp [p8048] at ha; subst a; trivial
  · exact checked8048
theorem derived8048 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8048 := by
  apply localUnsat_implies_entails f8048 [c7849, c8021, c8033, c8046, c8047, c2446, c1365, c638, c576, c2589, c7504, c2550, c1376] c8048 unsat8048 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8021 := derived8021 a h
  have h2 : Entails.eval a c8033 := derived8033 a h
  have h3 : Entails.eval a c8046 := derived8046 a h
  have h4 : Entails.eval a c8047 := derived8047 a h
  have h5 : Entails.eval a c2446 := h 2445 (by decide)
  have h6 : Entails.eval a c1365 := h 1364 (by decide)
  have h7 : Entails.eval a c638 := h 637 (by decide)
  have h8 : Entails.eval a c576 := h 575 (by decide)
  have h9 : Entails.eval a c2589 := h 2588 (by decide)
  have h10 : Entails.eval a c7504 := derived7504 a h
  have h11 : Entails.eval a c2550 := h 2549 (by decide)
  have h12 : Entails.eval a c1376 := h 1375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8049 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8049 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3071, some c3066, some c3343, some c3342, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false))]
def p8049 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8049 : lratChecker f8049 p8049 = .success := by decide +kernel
theorem unsat8049 : Unsatisfiable (PosFin 65) f8049 := by
  apply lratCheckerSound f8049 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8049
  · intro a ha; simp [p8049] at ha; subst a; trivial
  · exact checked8049
theorem derived8049 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8049 := by
  apply localUnsat_implies_entails f8049 [c3071, c3066, c3343, c3342] c8049 unsat8049 (by rfl) a
  have h0 : Entails.eval a c3071 := h 3070 (by decide)
  have h1 : Entails.eval a c3066 := h 3065 (by decide)
  have h2 : Entails.eval a c3343 := h 3342 (by decide)
  have h3 : Entails.eval a c3342 := h 3341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8050 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8050 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8021, some c8048, some c8049, some c3067, some c3070, some c3072, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8050 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8050 : lratChecker f8050 p8050 = .success := by decide +kernel
theorem unsat8050 : Unsatisfiable (PosFin 65) f8050 := by
  apply lratCheckerSound f8050 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8050
  · intro a ha; simp [p8050] at ha; subst a; trivial
  · exact checked8050
theorem derived8050 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8050 := by
  apply localUnsat_implies_entails f8050 [c8021, c8048, c8049, c3067, c3070, c3072] c8050 unsat8050 (by rfl) a
  have h0 : Entails.eval a c8021 := derived8021 a h
  have h1 : Entails.eval a c8048 := derived8048 a h
  have h2 : Entails.eval a c8049 := derived8049 a h
  have h3 : Entails.eval a c3067 := h 3066 (by decide)
  have h4 : Entails.eval a c3070 := h 3069 (by decide)
  have h5 : Entails.eval a c3072 := h 3071 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8051 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8051 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c521, some c854, some c682, some c2573, some c7958, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8051 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8051 : lratChecker f8051 p8051 = .success := by decide +kernel
theorem unsat8051 : Unsatisfiable (PosFin 65) f8051 := by
  apply lratCheckerSound f8051 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8051
  · intro a ha; simp [p8051] at ha; subst a; trivial
  · exact checked8051
theorem derived8051 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8051 := by
  apply localUnsat_implies_entails f8051 [c545, c553, c521, c854, c682, c2573, c7958] c8051 unsat8051 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c521 := h 520 (by decide)
  have h3 : Entails.eval a c854 := h 853 (by decide)
  have h4 : Entails.eval a c682 := h 681 (by decide)
  have h5 : Entails.eval a c2573 := h 2572 (by decide)
  have h6 : Entails.eval a c7958 := derived7958 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8052 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8052 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c860, some c862, some c854, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8052 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8052 : lratChecker f8052 p8052 = .success := by decide +kernel
theorem unsat8052 : Unsatisfiable (PosFin 65) f8052 := by
  apply lratCheckerSound f8052 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8052
  · intro a ha; simp [p8052] at ha; subst a; trivial
  · exact checked8052
theorem derived8052 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8052 := by
  apply localUnsat_implies_entails f8052 [c860, c862, c854] c8052 unsat8052 (by rfl) a
  have h0 : Entails.eval a c860 := h 859 (by decide)
  have h1 : Entails.eval a c862 := h 861 (by decide)
  have h2 : Entails.eval a c854 := h 853 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8053 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8053 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8046, some c8051, some c8052, some c2313, some c2314, some c2344, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8053 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8053 : lratChecker f8053 p8053 = .success := by decide +kernel
theorem unsat8053 : Unsatisfiable (PosFin 65) f8053 := by
  apply lratCheckerSound f8053 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8053
  · intro a ha; simp [p8053] at ha; subst a; trivial
  · exact checked8053
theorem derived8053 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8053 := by
  apply localUnsat_implies_entails f8053 [c8046, c8051, c8052, c2313, c2314, c2344] c8053 unsat8053 (by rfl) a
  have h0 : Entails.eval a c8046 := derived8046 a h
  have h1 : Entails.eval a c8051 := derived8051 a h
  have h2 : Entails.eval a c8052 := derived8052 a h
  have h3 : Entails.eval a c2313 := h 2312 (by decide)
  have h4 : Entails.eval a c2314 := h 2313 (by decide)
  have h5 : Entails.eval a c2344 := h 2343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8054 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8054 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7618, some c2417, some c1323, some c642, some c1341, some c1175, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8054 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8054 : lratChecker f8054 p8054 = .success := by decide +kernel
theorem unsat8054 : Unsatisfiable (PosFin 65) f8054 := by
  apply lratCheckerSound f8054 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8054
  · intro a ha; simp [p8054] at ha; subst a; trivial
  · exact checked8054
theorem derived8054 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8054 := by
  apply localUnsat_implies_entails f8054 [c7618, c2417, c1323, c642, c1341, c1175] c8054 unsat8054 (by rfl) a
  have h0 : Entails.eval a c7618 := derived7618 a h
  have h1 : Entails.eval a c2417 := h 2416 (by decide)
  have h2 : Entails.eval a c1323 := h 1322 (by decide)
  have h3 : Entails.eval a c642 := h 641 (by decide)
  have h4 : Entails.eval a c1341 := h 1340 (by decide)
  have h5 : Entails.eval a c1175 := h 1174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8055 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8055 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2416, some c2440, some c2418, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8055 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8055 : lratChecker f8055 p8055 = .success := by decide +kernel
theorem unsat8055 : Unsatisfiable (PosFin 65) f8055 := by
  apply lratCheckerSound f8055 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8055
  · intro a ha; simp [p8055] at ha; subst a; trivial
  · exact checked8055
theorem derived8055 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8055 := by
  apply localUnsat_implies_entails f8055 [c2416, c2440, c2418] c8055 unsat8055 (by rfl) a
  have h0 : Entails.eval a c2416 := h 2415 (by decide)
  have h1 : Entails.eval a c2440 := h 2439 (by decide)
  have h2 : Entails.eval a c2418 := h 2417 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8056 : DefaultClause 65 := directClause [(⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8056 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8053, some c8055, some c642, some c641, some c637, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8056 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8056 : lratChecker f8056 p8056 = .success := by decide +kernel
theorem unsat8056 : Unsatisfiable (PosFin 65) f8056 := by
  apply lratCheckerSound f8056 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8056
  · intro a ha; simp [p8056] at ha; subst a; trivial
  · exact checked8056
theorem derived8056 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8056 := by
  apply localUnsat_implies_entails f8056 [c8053, c8055, c642, c641, c637] c8056 unsat8056 (by rfl) a
  have h0 : Entails.eval a c8053 := derived8053 a h
  have h1 : Entails.eval a c8055 := derived8055 a h
  have h2 : Entails.eval a c642 := h 641 (by decide)
  have h3 : Entails.eval a c641 := h 640 (by decide)
  have h4 : Entails.eval a c637 := h 636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8057 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8057 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8053, some c8046, some c8056, some c2417, some c8054, some c1341, some c2280, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8057 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8057 : lratChecker f8057 p8057 = .success := by decide +kernel
theorem unsat8057 : Unsatisfiable (PosFin 65) f8057 := by
  apply lratCheckerSound f8057 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8057
  · intro a ha; simp [p8057] at ha; subst a; trivial
  · exact checked8057
theorem derived8057 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8057 := by
  apply localUnsat_implies_entails f8057 [c8053, c8046, c8056, c2417, c8054, c1341, c2280] c8057 unsat8057 (by rfl) a
  have h0 : Entails.eval a c8053 := derived8053 a h
  have h1 : Entails.eval a c8046 := derived8046 a h
  have h2 : Entails.eval a c8056 := derived8056 a h
  have h3 : Entails.eval a c2417 := h 2416 (by decide)
  have h4 : Entails.eval a c8054 := derived8054 a h
  have h5 : Entails.eval a c1341 := h 1340 (by decide)
  have h6 : Entails.eval a c2280 := h 2279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8058 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8058 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2417, some c1372, some c7618, some c1341, some c1830, some c2555, some c1175, some c1676, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8058 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8058 : lratChecker f8058 p8058 = .success := by decide +kernel
theorem unsat8058 : Unsatisfiable (PosFin 65) f8058 := by
  apply lratCheckerSound f8058 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8058
  · intro a ha; simp [p8058] at ha; subst a; trivial
  · exact checked8058
theorem derived8058 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8058 := by
  apply localUnsat_implies_entails f8058 [c2417, c1372, c7618, c1341, c1830, c2555, c1175, c1676] c8058 unsat8058 (by rfl) a
  have h0 : Entails.eval a c2417 := h 2416 (by decide)
  have h1 : Entails.eval a c1372 := h 1371 (by decide)
  have h2 : Entails.eval a c7618 := derived7618 a h
  have h3 : Entails.eval a c1341 := h 1340 (by decide)
  have h4 : Entails.eval a c1830 := h 1829 (by decide)
  have h5 : Entails.eval a c2555 := h 2554 (by decide)
  have h6 : Entails.eval a c1175 := h 1174 (by decide)
  have h7 : Entails.eval a c1676 := h 1675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8059 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8059 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7958, some c7610, some c1192, some c1187, some c7964, some c1102, some c1304, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8059 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8059 : lratChecker f8059 p8059 = .success := by decide +kernel
theorem unsat8059 : Unsatisfiable (PosFin 65) f8059 := by
  apply lratCheckerSound f8059 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8059
  · intro a ha; simp [p8059] at ha; subst a; trivial
  · exact checked8059
theorem derived8059 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8059 := by
  apply localUnsat_implies_entails f8059 [c7958, c7610, c1192, c1187, c7964, c1102, c1304] c8059 unsat8059 (by rfl) a
  have h0 : Entails.eval a c7958 := derived7958 a h
  have h1 : Entails.eval a c7610 := derived7610 a h
  have h2 : Entails.eval a c1192 := h 1191 (by decide)
  have h3 : Entails.eval a c1187 := h 1186 (by decide)
  have h4 : Entails.eval a c7964 := derived7964 a h
  have h5 : Entails.eval a c1102 := h 1101 (by decide)
  have h6 : Entails.eval a c1304 := h 1303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8060 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8060 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8021, some c8033, some c8050, some c8057, some c8053, some c8046, some c8058, some c7610, some c7958, some c8055, some c8059, some c7962, some c1362, some c7964, some c1102, some c1304, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8060 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8060 : lratChecker f8060 p8060 = .success := by decide +kernel
theorem unsat8060 : Unsatisfiable (PosFin 65) f8060 := by
  apply lratCheckerSound f8060 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8060
  · intro a ha; simp [p8060] at ha; subst a; trivial
  · exact checked8060
theorem derived8060 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8060 := by
  apply localUnsat_implies_entails f8060 [c7849, c8021, c8033, c8050, c8057, c8053, c8046, c8058, c7610, c7958, c8055, c8059, c7962, c1362, c7964, c1102, c1304] c8060 unsat8060 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8021 := derived8021 a h
  have h2 : Entails.eval a c8033 := derived8033 a h
  have h3 : Entails.eval a c8050 := derived8050 a h
  have h4 : Entails.eval a c8057 := derived8057 a h
  have h5 : Entails.eval a c8053 := derived8053 a h
  have h6 : Entails.eval a c8046 := derived8046 a h
  have h7 : Entails.eval a c8058 := derived8058 a h
  have h8 : Entails.eval a c7610 := derived7610 a h
  have h9 : Entails.eval a c7958 := derived7958 a h
  have h10 : Entails.eval a c8055 := derived8055 a h
  have h11 : Entails.eval a c8059 := derived8059 a h
  have h12 : Entails.eval a c7962 := derived7962 a h
  have h13 : Entails.eval a c1362 := h 1361 (by decide)
  have h14 : Entails.eval a c7964 := derived7964 a h
  have h15 : Entails.eval a c1102 := h 1101 (by decide)
  have h16 : Entails.eval a c1304 := h 1303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8061 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8061 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8050, some c8033, some c8021, some c7849, some c8057, some c8060, some c2313, some c2314, some c2344, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8061 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8061 : lratChecker f8061 p8061 = .success := by decide +kernel
theorem unsat8061 : Unsatisfiable (PosFin 65) f8061 := by
  apply lratCheckerSound f8061 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8061
  · intro a ha; simp [p8061] at ha; subst a; trivial
  · exact checked8061
theorem derived8061 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8061 := by
  apply localUnsat_implies_entails f8061 [c8050, c8033, c8021, c7849, c8057, c8060, c2313, c2314, c2344] c8061 unsat8061 (by rfl) a
  have h0 : Entails.eval a c8050 := derived8050 a h
  have h1 : Entails.eval a c8033 := derived8033 a h
  have h2 : Entails.eval a c8021 := derived8021 a h
  have h3 : Entails.eval a c7849 := derived7849 a h
  have h4 : Entails.eval a c8057 := derived8057 a h
  have h5 : Entails.eval a c8060 := derived8060 a h
  have h6 : Entails.eval a c2313 := h 2312 (by decide)
  have h7 : Entails.eval a c2314 := h 2313 (by decide)
  have h8 : Entails.eval a c2344 := h 2343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8062 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8062 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8052, some c524, some c525, some c545, some c682, some c532, some c551, some c2573, some c530, some c1331, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8062 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8062 : lratChecker f8062 p8062 = .success := by decide +kernel
theorem unsat8062 : Unsatisfiable (PosFin 65) f8062 := by
  apply lratCheckerSound f8062 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8062
  · intro a ha; simp [p8062] at ha; subst a; trivial
  · exact checked8062
theorem derived8062 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8062 := by
  apply localUnsat_implies_entails f8062 [c8052, c524, c525, c545, c682, c532, c551, c2573, c530, c1331] c8062 unsat8062 (by rfl) a
  have h0 : Entails.eval a c8052 := derived8052 a h
  have h1 : Entails.eval a c524 := h 523 (by decide)
  have h2 : Entails.eval a c525 := h 524 (by decide)
  have h3 : Entails.eval a c545 := h 544 (by decide)
  have h4 : Entails.eval a c682 := h 681 (by decide)
  have h5 : Entails.eval a c532 := h 531 (by decide)
  have h6 : Entails.eval a c551 := h 550 (by decide)
  have h7 : Entails.eval a c2573 := h 2572 (by decide)
  have h8 : Entails.eval a c530 := h 529 (by decide)
  have h9 : Entails.eval a c1331 := h 1330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8063 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨24, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8063 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8041, some c7617, some c7620, some c7846, some c7811, some c7762, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8063 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8063 : lratChecker f8063 p8063 = .success := by decide +kernel
theorem unsat8063 : Unsatisfiable (PosFin 65) f8063 := by
  apply lratCheckerSound f8063 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8063
  · intro a ha; simp [p8063] at ha; subst a; trivial
  · exact checked8063
theorem derived8063 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8063 := by
  apply localUnsat_implies_entails f8063 [c8041, c7617, c7620, c7846, c7811, c7762] c8063 unsat8063 (by rfl) a
  have h0 : Entails.eval a c8041 := derived8041 a h
  have h1 : Entails.eval a c7617 := derived7617 a h
  have h2 : Entails.eval a c7620 := derived7620 a h
  have h3 : Entails.eval a c7846 := derived7846 a h
  have h4 : Entails.eval a c7811 := derived7811 a h
  have h5 : Entails.eval a c7762 := derived7762 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8064 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8064 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8046, some c8052, some c8062, some c2324, some c8063, some c2344, some c2588, some c1460, some c2379, some c2373, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8064 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8064 : lratChecker f8064 p8064 = .success := by decide +kernel
theorem unsat8064 : Unsatisfiable (PosFin 65) f8064 := by
  apply lratCheckerSound f8064 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8064
  · intro a ha; simp [p8064] at ha; subst a; trivial
  · exact checked8064
theorem derived8064 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8064 := by
  apply localUnsat_implies_entails f8064 [c8046, c8052, c8062, c2324, c8063, c2344, c2588, c1460, c2379, c2373] c8064 unsat8064 (by rfl) a
  have h0 : Entails.eval a c8046 := derived8046 a h
  have h1 : Entails.eval a c8052 := derived8052 a h
  have h2 : Entails.eval a c8062 := derived8062 a h
  have h3 : Entails.eval a c2324 := h 2323 (by decide)
  have h4 : Entails.eval a c8063 := derived8063 a h
  have h5 : Entails.eval a c2344 := h 2343 (by decide)
  have h6 : Entails.eval a c2588 := h 2587 (by decide)
  have h7 : Entails.eval a c1460 := h 1459 (by decide)
  have h8 : Entails.eval a c2379 := h 2378 (by decide)
  have h9 : Entails.eval a c2373 := h 2372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8065 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨12, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8065 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1214, some c1301, some c1334, some c1311, some c2074, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8065 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8065 : lratChecker f8065 p8065 = .success := by decide +kernel
theorem unsat8065 : Unsatisfiable (PosFin 65) f8065 := by
  apply lratCheckerSound f8065 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8065
  · intro a ha; simp [p8065] at ha; subst a; trivial
  · exact checked8065
theorem derived8065 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8065 := by
  apply localUnsat_implies_entails f8065 [c1214, c1301, c1334, c1311, c2074] c8065 unsat8065 (by rfl) a
  have h0 : Entails.eval a c1214 := h 1213 (by decide)
  have h1 : Entails.eval a c1301 := h 1300 (by decide)
  have h2 : Entails.eval a c1334 := h 1333 (by decide)
  have h3 : Entails.eval a c1311 := h 1310 (by decide)
  have h4 : Entails.eval a c2074 := h 2073 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8066 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8066 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7618, some c8065, some c1329, some c1175, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8066 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8066 : lratChecker f8066 p8066 = .success := by decide +kernel
theorem unsat8066 : Unsatisfiable (PosFin 65) f8066 := by
  apply lratCheckerSound f8066 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8066
  · intro a ha; simp [p8066] at ha; subst a; trivial
  · exact checked8066
theorem derived8066 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8066 := by
  apply localUnsat_implies_entails f8066 [c7618, c8065, c1329, c1175] c8066 unsat8066 (by rfl) a
  have h0 : Entails.eval a c7618 := derived7618 a h
  have h1 : Entails.eval a c8065 := derived8065 a h
  have h2 : Entails.eval a c1329 := h 1328 (by decide)
  have h3 : Entails.eval a c1175 := h 1174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8067 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8067 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1329, some c2146, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p8067 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8067 : lratChecker f8067 p8067 = .success := by decide +kernel
theorem unsat8067 : Unsatisfiable (PosFin 65) f8067 := by
  apply lratCheckerSound f8067 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8067
  · intro a ha; simp [p8067] at ha; subst a; trivial
  · exact checked8067
theorem derived8067 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8067 := by
  apply localUnsat_implies_entails f8067 [c1329, c2146] c8067 unsat8067 (by rfl) a
  have h0 : Entails.eval a c1329 := h 1328 (by decide)
  have h1 : Entails.eval a c2146 := h 2145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8068 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8068 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8066, some c7617, some c8067, some c1448, some c1334, some c2074, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8068 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8068 : lratChecker f8068 p8068 = .success := by decide +kernel
theorem unsat8068 : Unsatisfiable (PosFin 65) f8068 := by
  apply lratCheckerSound f8068 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8068
  · intro a ha; simp [p8068] at ha; subst a; trivial
  · exact checked8068
theorem derived8068 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8068 := by
  apply localUnsat_implies_entails f8068 [c8066, c7617, c8067, c1448, c1334, c2074] c8068 unsat8068 (by rfl) a
  have h0 : Entails.eval a c8066 := derived8066 a h
  have h1 : Entails.eval a c7617 := derived7617 a h
  have h2 : Entails.eval a c8067 := derived8067 a h
  have h3 : Entails.eval a c1448 := h 1447 (by decide)
  have h4 : Entails.eval a c1334 := h 1333 (by decide)
  have h5 : Entails.eval a c2074 := h 2073 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8069 : DefaultClause 65 := directClause [(⟨13, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8069 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c513, some c1331, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8069 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8069 : lratChecker f8069 p8069 = .success := by decide +kernel
theorem unsat8069 : Unsatisfiable (PosFin 65) f8069 := by
  apply lratCheckerSound f8069 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8069
  · intro a ha; simp [p8069] at ha; subst a; trivial
  · exact checked8069
theorem derived8069 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8069 := by
  apply localUnsat_implies_entails f8069 [c513, c1331] c8069 unsat8069 (by rfl) a
  have h0 : Entails.eval a c513 := h 512 (by decide)
  have h1 : Entails.eval a c1331 := h 1330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8070 : DefaultClause 65 := directClause [(⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8070 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c444, some c2148, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8070 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8070 : lratChecker f8070 p8070 = .success := by decide +kernel
theorem unsat8070 : Unsatisfiable (PosFin 65) f8070 := by
  apply lratCheckerSound f8070 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8070
  · intro a ha; simp [p8070] at ha; subst a; trivial
  · exact checked8070
theorem derived8070 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8070 := by
  apply localUnsat_implies_entails f8070 [c444, c2148] c8070 unsat8070 (by rfl) a
  have h0 : Entails.eval a c444 := h 443 (by decide)
  have h1 : Entails.eval a c2148 := h 2147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8071 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8071 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8069, some c8070, some c929, some c451, some c2162, some c1167, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8071 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8071 : lratChecker f8071 p8071 = .success := by decide +kernel
theorem unsat8071 : Unsatisfiable (PosFin 65) f8071 := by
  apply lratCheckerSound f8071 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8071
  · intro a ha; simp [p8071] at ha; subst a; trivial
  · exact checked8071
theorem derived8071 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8071 := by
  apply localUnsat_implies_entails f8071 [c8069, c8070, c929, c451, c2162, c1167] c8071 unsat8071 (by rfl) a
  have h0 : Entails.eval a c8069 := derived8069 a h
  have h1 : Entails.eval a c8070 := derived8070 a h
  have h2 : Entails.eval a c929 := h 928 (by decide)
  have h3 : Entails.eval a c451 := h 450 (by decide)
  have h4 : Entails.eval a c2162 := h 2161 (by decide)
  have h5 : Entails.eval a c1167 := h 1166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8072 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8072 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1334, some c452, some c2156, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8072 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8072 : lratChecker f8072 p8072 = .success := by decide +kernel
theorem unsat8072 : Unsatisfiable (PosFin 65) f8072 := by
  apply lratCheckerSound f8072 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8072
  · intro a ha; simp [p8072] at ha; subst a; trivial
  · exact checked8072
theorem derived8072 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8072 := by
  apply localUnsat_implies_entails f8072 [c1334, c452, c2156] c8072 unsat8072 (by rfl) a
  have h0 : Entails.eval a c1334 := h 1333 (by decide)
  have h1 : Entails.eval a c452 := h 451 (by decide)
  have h2 : Entails.eval a c2156 := h 2155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8073 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8073 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8068, some c8072, some c8071, some c7617, some c7846, some c1364, some c2007, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8073 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8073 : lratChecker f8073 p8073 = .success := by decide +kernel
theorem unsat8073 : Unsatisfiable (PosFin 65) f8073 := by
  apply lratCheckerSound f8073 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8073
  · intro a ha; simp [p8073] at ha; subst a; trivial
  · exact checked8073
theorem derived8073 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8073 := by
  apply localUnsat_implies_entails f8073 [c8068, c8072, c8071, c7617, c7846, c1364, c2007] c8073 unsat8073 (by rfl) a
  have h0 : Entails.eval a c8068 := derived8068 a h
  have h1 : Entails.eval a c8072 := derived8072 a h
  have h2 : Entails.eval a c8071 := derived8071 a h
  have h3 : Entails.eval a c7617 := derived7617 a h
  have h4 : Entails.eval a c7846 := derived7846 a h
  have h5 : Entails.eval a c1364 := h 1363 (by decide)
  have h6 : Entails.eval a c2007 := h 2006 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8074 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8074 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8041, some c8063, some c7617, some c7623, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8074 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8074 : lratChecker f8074 p8074 = .success := by decide +kernel
theorem unsat8074 : Unsatisfiable (PosFin 65) f8074 := by
  apply lratCheckerSound f8074 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8074
  · intro a ha; simp [p8074] at ha; subst a; trivial
  · exact checked8074
theorem derived8074 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8074 := by
  apply localUnsat_implies_entails f8074 [c8041, c8063, c7617, c7623] c8074 unsat8074 (by rfl) a
  have h0 : Entails.eval a c8041 := derived8041 a h
  have h1 : Entails.eval a c8063 := derived8063 a h
  have h2 : Entails.eval a c7617 := derived7617 a h
  have h3 : Entails.eval a c7623 := derived7623 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8075 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8075 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2294, some c2293, some c7998, some c2445, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8075 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8075 : lratChecker f8075 p8075 = .success := by decide +kernel
theorem unsat8075 : Unsatisfiable (PosFin 65) f8075 := by
  apply lratCheckerSound f8075 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8075
  · intro a ha; simp [p8075] at ha; subst a; trivial
  · exact checked8075
theorem derived8075 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8075 := by
  apply localUnsat_implies_entails f8075 [c2294, c2293, c7998, c2445] c8075 unsat8075 (by rfl) a
  have h0 : Entails.eval a c2294 := h 2293 (by decide)
  have h1 : Entails.eval a c2293 := h 2292 (by decide)
  have h2 : Entails.eval a c7998 := derived7998 a h
  have h3 : Entails.eval a c2445 := h 2444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8076 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8076 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8064, some c8046, some c8073, some c8074, some c8075, some c7617, some c7846, some c7811, some c2007, some c1364, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8076 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8076 : lratChecker f8076 p8076 = .success := by decide +kernel
theorem unsat8076 : Unsatisfiable (PosFin 65) f8076 := by
  apply lratCheckerSound f8076 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8076
  · intro a ha; simp [p8076] at ha; subst a; trivial
  · exact checked8076
theorem derived8076 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8076 := by
  apply localUnsat_implies_entails f8076 [c8064, c8046, c8073, c8074, c8075, c7617, c7846, c7811, c2007, c1364] c8076 unsat8076 (by rfl) a
  have h0 : Entails.eval a c8064 := derived8064 a h
  have h1 : Entails.eval a c8046 := derived8046 a h
  have h2 : Entails.eval a c8073 := derived8073 a h
  have h3 : Entails.eval a c8074 := derived8074 a h
  have h4 : Entails.eval a c8075 := derived8075 a h
  have h5 : Entails.eval a c7617 := derived7617 a h
  have h6 : Entails.eval a c7846 := derived7846 a h
  have h7 : Entails.eval a c7811 := derived7811 a h
  have h8 : Entails.eval a c2007 := h 2006 (by decide)
  have h9 : Entails.eval a c1364 := h 1363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8077 : DefaultClause 65 := directClause [(⟨2, by decide⟩, false), (⟨13, by decide⟩, false), (⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8077 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1189, some c1185, some c1191, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8077 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8077 : lratChecker f8077 p8077 = .success := by decide +kernel
theorem unsat8077 : Unsatisfiable (PosFin 65) f8077 := by
  apply lratCheckerSound f8077 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8077
  · intro a ha; simp [p8077] at ha; subst a; trivial
  · exact checked8077
theorem derived8077 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8077 := by
  apply localUnsat_implies_entails f8077 [c1189, c1185, c1191] c8077 unsat8077 (by rfl) a
  have h0 : Entails.eval a c1189 := h 1188 (by decide)
  have h1 : Entails.eval a c1185 := h 1184 (by decide)
  have h2 : Entails.eval a c1191 := h 1190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8078 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8078 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8069, some c8077, some c904, some c929, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8078 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8078 : lratChecker f8078 p8078 = .success := by decide +kernel
theorem unsat8078 : Unsatisfiable (PosFin 65) f8078 := by
  apply lratCheckerSound f8078 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8078
  · intro a ha; simp [p8078] at ha; subst a; trivial
  · exact checked8078
theorem derived8078 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8078 := by
  apply localUnsat_implies_entails f8078 [c8069, c8077, c904, c929] c8078 unsat8078 (by rfl) a
  have h0 : Entails.eval a c8069 := derived8069 a h
  have h1 : Entails.eval a c8077 := derived8077 a h
  have h2 : Entails.eval a c904 := h 903 (by decide)
  have h3 : Entails.eval a c929 := h 928 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8079 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8079 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1334, some c1311, some c2613, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8079 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8079 : lratChecker f8079 p8079 = .success := by decide +kernel
theorem unsat8079 : Unsatisfiable (PosFin 65) f8079 := by
  apply lratCheckerSound f8079 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8079
  · intro a ha; simp [p8079] at ha; subst a; trivial
  · exact checked8079
theorem derived8079 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8079 := by
  apply localUnsat_implies_entails f8079 [c1334, c1311, c2613] c8079 unsat8079 (by rfl) a
  have h0 : Entails.eval a c1334 := h 1333 (by decide)
  have h1 : Entails.eval a c1311 := h 1310 (by decide)
  have h2 : Entails.eval a c2613 := h 2612 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8080 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8080 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8068, some c8079, some c8078, some c7617, some c7846, some c1364, some c2007, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8080 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8080 : lratChecker f8080 p8080 = .success := by decide +kernel
theorem unsat8080 : Unsatisfiable (PosFin 65) f8080 := by
  apply lratCheckerSound f8080 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8080
  · intro a ha; simp [p8080] at ha; subst a; trivial
  · exact checked8080
theorem derived8080 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8080 := by
  apply localUnsat_implies_entails f8080 [c8068, c8079, c8078, c7617, c7846, c1364, c2007] c8080 unsat8080 (by rfl) a
  have h0 : Entails.eval a c8068 := derived8068 a h
  have h1 : Entails.eval a c8079 := derived8079 a h
  have h2 : Entails.eval a c8078 := derived8078 a h
  have h3 : Entails.eval a c7617 := derived7617 a h
  have h4 : Entails.eval a c7846 := derived7846 a h
  have h5 : Entails.eval a c1364 := h 1363 (by decide)
  have h6 : Entails.eval a c2007 := h 2006 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8080

end CochromaticTwenty.Certificates.FixedCore1
