import MerLeanExperiment.Certificates.FixedCore1.Steps2100_2199

/-! Generated from the actual pinned fixed_core1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c8081 : DefaultClause 65 := directClause [(⟨32, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8081 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8021, some c8033, some c8046, some c8050, some c8061, some c8064, some c8076, some c8080, some c2324, some c8074, some c2344, some c2588, some c1460, some c2379, some c2373, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8081 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked8081 : lratChecker f8081 p8081 = .success := by decide +kernel
theorem unsat8081 : Unsatisfiable (PosFin 65) f8081 := by
  apply lratCheckerSound f8081 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8081
  · intro a ha; simp [p8081] at ha; subst a; trivial
  · exact checked8081
theorem derived8081 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8081 := by
  apply localUnsat_implies_entails f8081 [c7849, c8021, c8033, c8046, c8050, c8061, c8064, c8076, c8080, c2324, c8074, c2344, c2588, c1460, c2379, c2373] c8081 unsat8081 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8021 := derived8021 a h
  have h2 : Entails.eval a c8033 := derived8033 a h
  have h3 : Entails.eval a c8046 := derived8046 a h
  have h4 : Entails.eval a c8050 := derived8050 a h
  have h5 : Entails.eval a c8061 := derived8061 a h
  have h6 : Entails.eval a c8064 := derived8064 a h
  have h7 : Entails.eval a c8076 := derived8076 a h
  have h8 : Entails.eval a c8080 := derived8080 a h
  have h9 : Entails.eval a c2324 := h 2323 (by decide)
  have h10 : Entails.eval a c8074 := derived8074 a h
  have h11 : Entails.eval a c2344 := h 2343 (by decide)
  have h12 : Entails.eval a c2588 := h 2587 (by decide)
  have h13 : Entails.eval a c1460 := h 1459 (by decide)
  have h14 : Entails.eval a c2379 := h 2378 (by decide)
  have h15 : Entails.eval a c2373 := h 2372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8082 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8082 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7672, some c1468, some c2674, some c844, some c1180, some c2300, some c499, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8082 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8082 : lratChecker f8082 p8082 = .success := by decide +kernel
theorem unsat8082 : Unsatisfiable (PosFin 65) f8082 := by
  apply lratCheckerSound f8082 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8082
  · intro a ha; simp [p8082] at ha; subst a; trivial
  · exact checked8082
theorem derived8082 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8082 := by
  apply localUnsat_implies_entails f8082 [c7672, c1468, c2674, c844, c1180, c2300, c499] c8082 unsat8082 (by rfl) a
  have h0 : Entails.eval a c7672 := derived7672 a h
  have h1 : Entails.eval a c1468 := h 1467 (by decide)
  have h2 : Entails.eval a c2674 := h 2673 (by decide)
  have h3 : Entails.eval a c844 := h 843 (by decide)
  have h4 : Entails.eval a c1180 := h 1179 (by decide)
  have h5 : Entails.eval a c2300 := h 2299 (by decide)
  have h6 : Entails.eval a c499 := h 498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8083 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8083 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7570, some c1470, some c845, some c2675, some c1180, some c499, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8083 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8083 : lratChecker f8083 p8083 = .success := by decide +kernel
theorem unsat8083 : Unsatisfiable (PosFin 65) f8083 := by
  apply lratCheckerSound f8083 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8083
  · intro a ha; simp [p8083] at ha; subst a; trivial
  · exact checked8083
theorem derived8083 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8083 := by
  apply localUnsat_implies_entails f8083 [c7570, c1470, c845, c2675, c1180, c499] c8083 unsat8083 (by rfl) a
  have h0 : Entails.eval a c7570 := derived7570 a h
  have h1 : Entails.eval a c1470 := h 1469 (by decide)
  have h2 : Entails.eval a c845 := h 844 (by decide)
  have h3 : Entails.eval a c2675 := h 2674 (by decide)
  have h4 : Entails.eval a c1180 := h 1179 (by decide)
  have h5 : Entails.eval a c499 := h 498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8084 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8084 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7916, some c8082, some c8083, some c7989, some c522, some c854, some c554, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8084 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8084 : lratChecker f8084 p8084 = .success := by decide +kernel
theorem unsat8084 : Unsatisfiable (PosFin 65) f8084 := by
  apply lratCheckerSound f8084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8084
  · intro a ha; simp [p8084] at ha; subst a; trivial
  · exact checked8084
theorem derived8084 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8084 := by
  apply localUnsat_implies_entails f8084 [c7916, c8082, c8083, c7989, c522, c854, c554] c8084 unsat8084 (by rfl) a
  have h0 : Entails.eval a c7916 := derived7916 a h
  have h1 : Entails.eval a c8082 := derived8082 a h
  have h2 : Entails.eval a c8083 := derived8083 a h
  have h3 : Entails.eval a c7989 := derived7989 a h
  have h4 : Entails.eval a c522 := h 521 (by decide)
  have h5 : Entails.eval a c854 := h 853 (by decide)
  have h6 : Entails.eval a c554 := h 553 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8085 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8085 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7916, some c8082, some c8084, some c8024, some c8025, some c2675, some c1470, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8085 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8085 : lratChecker f8085 p8085 = .success := by decide +kernel
theorem unsat8085 : Unsatisfiable (PosFin 65) f8085 := by
  apply lratCheckerSound f8085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8085
  · intro a ha; simp [p8085] at ha; subst a; trivial
  · exact checked8085
theorem derived8085 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8085 := by
  apply localUnsat_implies_entails f8085 [c7916, c8082, c8084, c8024, c8025, c2675, c1470] c8085 unsat8085 (by rfl) a
  have h0 : Entails.eval a c7916 := derived7916 a h
  have h1 : Entails.eval a c8082 := derived8082 a h
  have h2 : Entails.eval a c8084 := derived8084 a h
  have h3 : Entails.eval a c8024 := derived8024 a h
  have h4 : Entails.eval a c8025 := derived8025 a h
  have h5 : Entails.eval a c2675 := h 2674 (by decide)
  have h6 : Entails.eval a c1470 := h 1469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8086 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8086 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8085, some c8082, some c8083, some c7989, some c851, some c854, some c838, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8086 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8086 : lratChecker f8086 p8086 = .success := by decide +kernel
theorem unsat8086 : Unsatisfiable (PosFin 65) f8086 := by
  apply lratCheckerSound f8086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8086
  · intro a ha; simp [p8086] at ha; subst a; trivial
  · exact checked8086
theorem derived8086 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8086 := by
  apply localUnsat_implies_entails f8086 [c8085, c8082, c8083, c7989, c851, c854, c838] c8086 unsat8086 (by rfl) a
  have h0 : Entails.eval a c8085 := derived8085 a h
  have h1 : Entails.eval a c8082 := derived8082 a h
  have h2 : Entails.eval a c8083 := derived8083 a h
  have h3 : Entails.eval a c7989 := derived7989 a h
  have h4 : Entails.eval a c851 := h 850 (by decide)
  have h5 : Entails.eval a c854 := h 853 (by decide)
  have h6 : Entails.eval a c838 := h 837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8087 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8087 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1506, some c1507, some c1511, some c1525, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8087 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8087 : lratChecker f8087 p8087 = .success := by decide +kernel
theorem unsat8087 : Unsatisfiable (PosFin 65) f8087 := by
  apply lratCheckerSound f8087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8087
  · intro a ha; simp [p8087] at ha; subst a; trivial
  · exact checked8087
theorem derived8087 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8087 := by
  apply localUnsat_implies_entails f8087 [c1506, c1507, c1511, c1525] c8087 unsat8087 (by rfl) a
  have h0 : Entails.eval a c1506 := h 1505 (by decide)
  have h1 : Entails.eval a c1507 := h 1506 (by decide)
  have h2 : Entails.eval a c1511 := h 1510 (by decide)
  have h3 : Entails.eval a c1525 := h 1524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8088 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8088 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8082, some c8086, some c8024, some c8025, some c2675, some c1470, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8088 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8088 : lratChecker f8088 p8088 = .success := by decide +kernel
theorem unsat8088 : Unsatisfiable (PosFin 65) f8088 := by
  apply lratCheckerSound f8088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8088
  · intro a ha; simp [p8088] at ha; subst a; trivial
  · exact checked8088
theorem derived8088 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8088 := by
  apply localUnsat_implies_entails f8088 [c8082, c8086, c8024, c8025, c2675, c1470] c8088 unsat8088 (by rfl) a
  have h0 : Entails.eval a c8082 := derived8082 a h
  have h1 : Entails.eval a c8086 := derived8086 a h
  have h2 : Entails.eval a c8024 := derived8024 a h
  have h3 : Entails.eval a c8025 := derived8025 a h
  have h4 : Entails.eval a c2675 := h 2674 (by decide)
  have h5 : Entails.eval a c1470 := h 1469 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8089 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8089 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8087, some c8088, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8089 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8089 : lratChecker f8089 p8089 = .success := by decide +kernel
theorem unsat8089 : Unsatisfiable (PosFin 65) f8089 := by
  apply lratCheckerSound f8089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8089
  · intro a ha; simp [p8089] at ha; subst a; trivial
  · exact checked8089
theorem derived8089 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8089 := by
  apply localUnsat_implies_entails f8089 [c8087, c8088] c8089 unsat8089 (by rfl) a
  have h0 : Entails.eval a c8087 := derived8087 a h
  have h1 : Entails.eval a c8088 := derived8088 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8090 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8090 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c844, some c434, some c499, some c2272, some c2076, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8090 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8090 : lratChecker f8090 p8090 = .success := by decide +kernel
theorem unsat8090 : Unsatisfiable (PosFin 65) f8090 := by
  apply lratCheckerSound f8090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8090
  · intro a ha; simp [p8090] at ha; subst a; trivial
  · exact checked8090
theorem derived8090 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8090 := by
  apply localUnsat_implies_entails f8090 [c844, c434, c499, c2272, c2076] c8090 unsat8090 (by rfl) a
  have h0 : Entails.eval a c844 := h 843 (by decide)
  have h1 : Entails.eval a c434 := h 433 (by decide)
  have h2 : Entails.eval a c499 := h 498 (by decide)
  have h3 : Entails.eval a c2272 := h 2271 (by decide)
  have h4 : Entails.eval a c2076 := h 2075 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8091 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8091 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8089, some c7678, some c1022, some c521, some c1176, some c845, some c499, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8091 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8091 : lratChecker f8091 p8091 = .success := by decide +kernel
theorem unsat8091 : Unsatisfiable (PosFin 65) f8091 := by
  apply lratCheckerSound f8091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8091
  · intro a ha; simp [p8091] at ha; subst a; trivial
  · exact checked8091
theorem derived8091 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8091 := by
  apply localUnsat_implies_entails f8091 [c8089, c7678, c1022, c521, c1176, c845, c499] c8091 unsat8091 (by rfl) a
  have h0 : Entails.eval a c8089 := derived8089 a h
  have h1 : Entails.eval a c7678 := derived7678 a h
  have h2 : Entails.eval a c1022 := h 1021 (by decide)
  have h3 : Entails.eval a c521 := h 520 (by decide)
  have h4 : Entails.eval a c1176 := h 1175 (by decide)
  have h5 : Entails.eval a c845 := h 844 (by decide)
  have h6 : Entails.eval a c499 := h 498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8092 : DefaultClause 65 := directClause [(⟨12, by decide⟩, false), (⟨20, by decide⟩, false), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨25, by decide⟩, true), (⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8092 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7896, some c7902, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8092 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8092 : lratChecker f8092 p8092 = .success := by decide +kernel
theorem unsat8092 : Unsatisfiable (PosFin 65) f8092 := by
  apply lratCheckerSound f8092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8092
  · intro a ha; simp [p8092] at ha; subst a; trivial
  · exact checked8092
theorem derived8092 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8092 := by
  apply localUnsat_implies_entails f8092 [c7896, c7902] c8092 unsat8092 (by rfl) a
  have h0 : Entails.eval a c7896 := derived7896 a h
  have h1 : Entails.eval a c7902 := derived7902 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8093 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8093 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8089, some c8091, some c7961, some c7920, some c8092, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8093 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8093 : lratChecker f8093 p8093 = .success := by decide +kernel
theorem unsat8093 : Unsatisfiable (PosFin 65) f8093 := by
  apply lratCheckerSound f8093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8093
  · intro a ha; simp [p8093] at ha; subst a; trivial
  · exact checked8093
theorem derived8093 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8093 := by
  apply localUnsat_implies_entails f8093 [c8089, c8091, c7961, c7920, c8092] c8093 unsat8093 (by rfl) a
  have h0 : Entails.eval a c8089 := derived8089 a h
  have h1 : Entails.eval a c8091 := derived8091 a h
  have h2 : Entails.eval a c7961 := derived7961 a h
  have h3 : Entails.eval a c7920 := derived7920 a h
  have h4 : Entails.eval a c8092 := derived8092 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8094 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8094 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1022, some c7995, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8094 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8094 : lratChecker f8094 p8094 = .success := by decide +kernel
theorem unsat8094 : Unsatisfiable (PosFin 65) f8094 := by
  apply lratCheckerSound f8094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8094
  · intro a ha; simp [p8094] at ha; subst a; trivial
  · exact checked8094
theorem derived8094 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8094 := by
  apply localUnsat_implies_entails f8094 [c1022, c7995] c8094 unsat8094 (by rfl) a
  have h0 : Entails.eval a c1022 := h 1021 (by decide)
  have h1 : Entails.eval a c7995 := derived7995 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8095 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8095 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c434, some c499, some c2272, some c2076, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8095 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8095 : lratChecker f8095 p8095 = .success := by decide +kernel
theorem unsat8095 : Unsatisfiable (PosFin 65) f8095 := by
  apply lratCheckerSound f8095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8095
  · intro a ha; simp [p8095] at ha; subst a; trivial
  · exact checked8095
theorem derived8095 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8095 := by
  apply localUnsat_implies_entails f8095 [c434, c499, c2272, c2076] c8095 unsat8095 (by rfl) a
  have h0 : Entails.eval a c434 := h 433 (by decide)
  have h1 : Entails.eval a c499 := h 498 (by decide)
  have h2 : Entails.eval a c2272 := h 2271 (by decide)
  have h3 : Entails.eval a c2076 := h 2075 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8096 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8096 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8089, some c8093, some c8094, some c8095, some c531, some c530, some c555, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8096 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8096 : lratChecker f8096 p8096 = .success := by decide +kernel
theorem unsat8096 : Unsatisfiable (PosFin 65) f8096 := by
  apply lratCheckerSound f8096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8096
  · intro a ha; simp [p8096] at ha; subst a; trivial
  · exact checked8096
theorem derived8096 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8096 := by
  apply localUnsat_implies_entails f8096 [c8089, c8093, c8094, c8095, c531, c530, c555] c8096 unsat8096 (by rfl) a
  have h0 : Entails.eval a c8089 := derived8089 a h
  have h1 : Entails.eval a c8093 := derived8093 a h
  have h2 : Entails.eval a c8094 := derived8094 a h
  have h3 : Entails.eval a c8095 := derived8095 a h
  have h4 : Entails.eval a c531 := h 530 (by decide)
  have h5 : Entails.eval a c530 := h 529 (by decide)
  have h6 : Entails.eval a c555 := h 554 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8097 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8097 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8089, some c8096, some c1497, some c1472, some c548, some c531, some c529, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8097 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8097 : lratChecker f8097 p8097 = .success := by decide +kernel
theorem unsat8097 : Unsatisfiable (PosFin 65) f8097 := by
  apply lratCheckerSound f8097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8097
  · intro a ha; simp [p8097] at ha; subst a; trivial
  · exact checked8097
theorem derived8097 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8097 := by
  apply localUnsat_implies_entails f8097 [c8089, c8096, c1497, c1472, c548, c531, c529] c8097 unsat8097 (by rfl) a
  have h0 : Entails.eval a c8089 := derived8089 a h
  have h1 : Entails.eval a c8096 := derived8096 a h
  have h2 : Entails.eval a c1497 := h 1496 (by decide)
  have h3 : Entails.eval a c1472 := h 1471 (by decide)
  have h4 : Entails.eval a c548 := h 547 (by decide)
  have h5 : Entails.eval a c531 := h 530 (by decide)
  have h6 : Entails.eval a c529 := h 528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8098 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8098 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c634, some c645, some c625, some c622, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p8098 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8098 : lratChecker f8098 p8098 = .success := by decide +kernel
theorem unsat8098 : Unsatisfiable (PosFin 65) f8098 := by
  apply lratCheckerSound f8098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8098
  · intro a ha; simp [p8098] at ha; subst a; trivial
  · exact checked8098
theorem derived8098 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8098 := by
  apply localUnsat_implies_entails f8098 [c634, c645, c625, c622] c8098 unsat8098 (by rfl) a
  have h0 : Entails.eval a c634 := h 633 (by decide)
  have h1 : Entails.eval a c645 := h 644 (by decide)
  have h2 : Entails.eval a c625 := h 624 (by decide)
  have h3 : Entails.eval a c622 := h 621 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8099 : DefaultClause 65 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8099 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8089, some c8002, some c8009, some c8098, some c1497, some c2332, some c2333, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8099 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8099 : lratChecker f8099 p8099 = .success := by decide +kernel
theorem unsat8099 : Unsatisfiable (PosFin 65) f8099 := by
  apply lratCheckerSound f8099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8099
  · intro a ha; simp [p8099] at ha; subst a; trivial
  · exact checked8099
theorem derived8099 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8099 := by
  apply localUnsat_implies_entails f8099 [c8089, c8002, c8009, c8098, c1497, c2332, c2333] c8099 unsat8099 (by rfl) a
  have h0 : Entails.eval a c8089 := derived8089 a h
  have h1 : Entails.eval a c8002 := derived8002 a h
  have h2 : Entails.eval a c8009 := derived8009 a h
  have h3 : Entails.eval a c8098 := derived8098 a h
  have h4 : Entails.eval a c1497 := h 1496 (by decide)
  have h5 : Entails.eval a c2332 := h 2331 (by decide)
  have h6 : Entails.eval a c2333 := h 2332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8100 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨25, by decide⟩, true), (⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8100 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2420, some c2436, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8100 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8100 : lratChecker f8100 p8100 = .success := by decide +kernel
theorem unsat8100 : Unsatisfiable (PosFin 65) f8100 := by
  apply lratCheckerSound f8100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8100
  · intro a ha; simp [p8100] at ha; subst a; trivial
  · exact checked8100
theorem derived8100 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8100 := by
  apply localUnsat_implies_entails f8100 [c2420, c2436] c8100 unsat8100 (by rfl) a
  have h0 : Entails.eval a c2420 := h 2419 (by decide)
  have h1 : Entails.eval a c2436 := h 2435 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8101 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8101 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2587, some c499, some c1822, some c1640, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8101 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8101 : lratChecker f8101 p8101 = .success := by decide +kernel
theorem unsat8101 : Unsatisfiable (PosFin 65) f8101 := by
  apply lratCheckerSound f8101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8101
  · intro a ha; simp [p8101] at ha; subst a; trivial
  · exact checked8101
theorem derived8101 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8101 := by
  apply localUnsat_implies_entails f8101 [c2587, c499, c1822, c1640] c8101 unsat8101 (by rfl) a
  have h0 : Entails.eval a c2587 := h 2586 (by decide)
  have h1 : Entails.eval a c499 := h 498 (by decide)
  have h2 : Entails.eval a c1822 := h 1821 (by decide)
  have h3 : Entails.eval a c1640 := h 1639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8102 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8102 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8089, some c8099, some c8097, some c1510, some c1509, some c7924, some c1501, some c8100, some c8098, some c1497, some c1486, some c1494, some c1514, some c1526, some c8101, some c585, some c1842, some c1672, some c2564, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8102 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked8102 : lratChecker f8102 p8102 = .success := by decide +kernel
theorem unsat8102 : Unsatisfiable (PosFin 65) f8102 := by
  apply lratCheckerSound f8102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8102
  · intro a ha; simp [p8102] at ha; subst a; trivial
  · exact checked8102
theorem derived8102 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8102 := by
  apply localUnsat_implies_entails f8102 [c8089, c8099, c8097, c1510, c1509, c7924, c1501, c8100, c8098, c1497, c1486, c1494, c1514, c1526, c8101, c585, c1842, c1672, c2564] c8102 unsat8102 (by rfl) a
  have h0 : Entails.eval a c8089 := derived8089 a h
  have h1 : Entails.eval a c8099 := derived8099 a h
  have h2 : Entails.eval a c8097 := derived8097 a h
  have h3 : Entails.eval a c1510 := h 1509 (by decide)
  have h4 : Entails.eval a c1509 := h 1508 (by decide)
  have h5 : Entails.eval a c7924 := derived7924 a h
  have h6 : Entails.eval a c1501 := h 1500 (by decide)
  have h7 : Entails.eval a c8100 := derived8100 a h
  have h8 : Entails.eval a c8098 := derived8098 a h
  have h9 : Entails.eval a c1497 := h 1496 (by decide)
  have h10 : Entails.eval a c1486 := h 1485 (by decide)
  have h11 : Entails.eval a c1494 := h 1493 (by decide)
  have h12 : Entails.eval a c1514 := h 1513 (by decide)
  have h13 : Entails.eval a c1526 := h 1525 (by decide)
  have h14 : Entails.eval a c8101 := derived8101 a h
  have h15 : Entails.eval a c585 := h 584 (by decide)
  have h16 : Entails.eval a c1842 := h 1841 (by decide)
  have h17 : Entails.eval a c1672 := h 1671 (by decide)
  have h18 : Entails.eval a c2564 := h 2563 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8103 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8103 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c541, some c521, some c544, some c519, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8103 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8103 : lratChecker f8103 p8103 = .success := by decide +kernel
theorem unsat8103 : Unsatisfiable (PosFin 65) f8103 := by
  apply lratCheckerSound f8103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8103
  · intro a ha; simp [p8103] at ha; subst a; trivial
  · exact checked8103
theorem derived8103 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8103 := by
  apply localUnsat_implies_entails f8103 [c541, c521, c544, c519] c8103 unsat8103 (by rfl) a
  have h0 : Entails.eval a c541 := h 540 (by decide)
  have h1 : Entails.eval a c521 := h 520 (by decide)
  have h2 : Entails.eval a c544 := h 543 (by decide)
  have h3 : Entails.eval a c519 := h 518 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8104 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8104 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c906, some c1308, some c1036, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8104 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8104 : lratChecker f8104 p8104 = .success := by decide +kernel
theorem unsat8104 : Unsatisfiable (PosFin 65) f8104 := by
  apply lratCheckerSound f8104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8104
  · intro a ha; simp [p8104] at ha; subst a; trivial
  · exact checked8104
theorem derived8104 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8104 := by
  apply localUnsat_implies_entails f8104 [c906, c1308, c1036] c8104 unsat8104 (by rfl) a
  have h0 : Entails.eval a c906 := h 905 (by decide)
  have h1 : Entails.eval a c1308 := h 1307 (by decide)
  have h2 : Entails.eval a c1036 := h 1035 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8105 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8105 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8104, some c1320, some c2413, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8105 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8105 : lratChecker f8105 p8105 = .success := by decide +kernel
theorem unsat8105 : Unsatisfiable (PosFin 65) f8105 := by
  apply lratCheckerSound f8105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8105
  · intro a ha; simp [p8105] at ha; subst a; trivial
  · exact checked8105
theorem derived8105 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8105 := by
  apply localUnsat_implies_entails f8105 [c8104, c1320, c2413] c8105 unsat8105 (by rfl) a
  have h0 : Entails.eval a c8104 := derived8104 a h
  have h1 : Entails.eval a c1320 := h 1319 (by decide)
  have h2 : Entails.eval a c2413 := h 2412 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8106 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8106 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2274, some c2584, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8106 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8106 : lratChecker f8106 p8106 = .success := by decide +kernel
theorem unsat8106 : Unsatisfiable (PosFin 65) f8106 := by
  apply lratCheckerSound f8106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8106
  · intro a ha; simp [p8106] at ha; subst a; trivial
  · exact checked8106
theorem derived8106 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8106 := by
  apply localUnsat_implies_entails f8106 [c2274, c2584] c8106 unsat8106 (by rfl) a
  have h0 : Entails.eval a c2274 := h 2273 (by decide)
  have h1 : Entails.eval a c2584 := h 2583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8107 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8107 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1308, some c2585, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8107 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8107 : lratChecker f8107 p8107 = .success := by decide +kernel
theorem unsat8107 : Unsatisfiable (PosFin 65) f8107 := by
  apply lratCheckerSound f8107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8107
  · intro a ha; simp [p8107] at ha; subst a; trivial
  · exact checked8107
theorem derived8107 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8107 := by
  apply localUnsat_implies_entails f8107 [c1308, c2585] c8107 unsat8107 (by rfl) a
  have h0 : Entails.eval a c1308 := h 1307 (by decide)
  have h1 : Entails.eval a c2585 := h 2584 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8108 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8108 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8102, some c8105, some c8098, some c8107, some c1320, some c2593, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8108 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8108 : lratChecker f8108 p8108 = .success := by decide +kernel
theorem unsat8108 : Unsatisfiable (PosFin 65) f8108 := by
  apply lratCheckerSound f8108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8108
  · intro a ha; simp [p8108] at ha; subst a; trivial
  · exact checked8108
theorem derived8108 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8108 := by
  apply localUnsat_implies_entails f8108 [c8102, c8105, c8098, c8107, c1320, c2593] c8108 unsat8108 (by rfl) a
  have h0 : Entails.eval a c8102 := derived8102 a h
  have h1 : Entails.eval a c8105 := derived8105 a h
  have h2 : Entails.eval a c8098 := derived8098 a h
  have h3 : Entails.eval a c8107 := derived8107 a h
  have h4 : Entails.eval a c1320 := h 1319 (by decide)
  have h5 : Entails.eval a c2593 := h 2592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8109 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8109 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2212, some c2189, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8109 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8109 : lratChecker f8109 p8109 = .success := by decide +kernel
theorem unsat8109 : Unsatisfiable (PosFin 65) f8109 := by
  apply lratCheckerSound f8109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8109
  · intro a ha; simp [p8109] at ha; subst a; trivial
  · exact checked8109
theorem derived8109 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8109 := by
  apply localUnsat_implies_entails f8109 [c2212, c2189] c8109 unsat8109 (by rfl) a
  have h0 : Entails.eval a c2212 := h 2211 (by decide)
  have h1 : Entails.eval a c2189 := h 2188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8110 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8110 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8108, some c8109, some c8098, some c2345, some c2320, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8110 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8110 : lratChecker f8110 p8110 = .success := by decide +kernel
theorem unsat8110 : Unsatisfiable (PosFin 65) f8110 := by
  apply lratCheckerSound f8110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8110
  · intro a ha; simp [p8110] at ha; subst a; trivial
  · exact checked8110
theorem derived8110 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8110 := by
  apply localUnsat_implies_entails f8110 [c8108, c8109, c8098, c2345, c2320] c8110 unsat8110 (by rfl) a
  have h0 : Entails.eval a c8108 := derived8108 a h
  have h1 : Entails.eval a c8109 := derived8109 a h
  have h2 : Entails.eval a c8098 := derived8098 a h
  have h3 : Entails.eval a c2345 := h 2344 (by decide)
  have h4 : Entails.eval a c2320 := h 2319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8111 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8111 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8090, some c8095, some c533, some c528, some c855, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8111 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8111 : lratChecker f8111 p8111 = .success := by decide +kernel
theorem unsat8111 : Unsatisfiable (PosFin 65) f8111 := by
  apply lratCheckerSound f8111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8111
  · intro a ha; simp [p8111] at ha; subst a; trivial
  · exact checked8111
theorem derived8111 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8111 := by
  apply localUnsat_implies_entails f8111 [c8090, c8095, c533, c528, c855] c8111 unsat8111 (by rfl) a
  have h0 : Entails.eval a c8090 := derived8090 a h
  have h1 : Entails.eval a c8095 := derived8095 a h
  have h2 : Entails.eval a c533 := h 532 (by decide)
  have h3 : Entails.eval a c528 := h 527 (by decide)
  have h4 : Entails.eval a c855 := h 854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8112 : DefaultClause 65 := directClause [(⟨16, by decide⟩, false), (⟨7, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8112 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2424, some c2425, some c8100, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8112 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8112 : lratChecker f8112 p8112 = .success := by decide +kernel
theorem unsat8112 : Unsatisfiable (PosFin 65) f8112 := by
  apply lratCheckerSound f8112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8112
  · intro a ha; simp [p8112] at ha; subst a; trivial
  · exact checked8112
theorem derived8112 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8112 := by
  apply localUnsat_implies_entails f8112 [c2424, c2425, c8100] c8112 unsat8112 (by rfl) a
  have h0 : Entails.eval a c2424 := h 2423 (by decide)
  have h1 : Entails.eval a c2425 := h 2424 (by decide)
  have h2 : Entails.eval a c8100 := derived8100 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8113 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8113 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8110, some c8098, some c8111, some c8112, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8113 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8113 : lratChecker f8113 p8113 = .success := by decide +kernel
theorem unsat8113 : Unsatisfiable (PosFin 65) f8113 := by
  apply lratCheckerSound f8113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8113
  · intro a ha; simp [p8113] at ha; subst a; trivial
  · exact checked8113
theorem derived8113 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8113 := by
  apply localUnsat_implies_entails f8113 [c8110, c8098, c8111, c8112] c8113 unsat8113 (by rfl) a
  have h0 : Entails.eval a c8110 := derived8110 a h
  have h1 : Entails.eval a c8098 := derived8098 a h
  have h2 : Entails.eval a c8111 := derived8111 a h
  have h3 : Entails.eval a c8112 := derived8112 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8114 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8114 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c903, some c1330, some c8103, some c7343, some c1176, some c528, some c7419, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8114 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8114 : lratChecker f8114 p8114 = .success := by decide +kernel
theorem unsat8114 : Unsatisfiable (PosFin 65) f8114 := by
  apply lratCheckerSound f8114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8114
  · intro a ha; simp [p8114] at ha; subst a; trivial
  · exact checked8114
theorem derived8114 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8114 := by
  apply localUnsat_implies_entails f8114 [c903, c1330, c8103, c7343, c1176, c528, c7419] c8114 unsat8114 (by rfl) a
  have h0 : Entails.eval a c903 := h 902 (by decide)
  have h1 : Entails.eval a c1330 := h 1329 (by decide)
  have h2 : Entails.eval a c8103 := derived8103 a h
  have h3 : Entails.eval a c7343 := derived7343 a h
  have h4 : Entails.eval a c1176 := h 1175 (by decide)
  have h5 : Entails.eval a c528 := h 527 (by decide)
  have h6 : Entails.eval a c7419 := derived7419 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8115 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8115 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1303, some c2579, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8115 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8115 : lratChecker f8115 p8115 = .success := by decide +kernel
theorem unsat8115 : Unsatisfiable (PosFin 65) f8115 := by
  apply lratCheckerSound f8115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8115
  · intro a ha; simp [p8115] at ha; subst a; trivial
  · exact checked8115
theorem derived8115 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8115 := by
  apply localUnsat_implies_entails f8115 [c1303, c2579] c8115 unsat8115 (by rfl) a
  have h0 : Entails.eval a c1303 := h 1302 (by decide)
  have h1 : Entails.eval a c2579 := h 2578 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8116 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8116 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c548, some c531, some c529, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8116 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8116 : lratChecker f8116 p8116 = .success := by decide +kernel
theorem unsat8116 : Unsatisfiable (PosFin 65) f8116 := by
  apply lratCheckerSound f8116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8116
  · intro a ha; simp [p8116] at ha; subst a; trivial
  · exact checked8116
theorem derived8116 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8116 := by
  apply localUnsat_implies_entails f8116 [c548, c531, c529] c8116 unsat8116 (by rfl) a
  have h0 : Entails.eval a c548 := h 547 (by decide)
  have h1 : Entails.eval a c531 := h 530 (by decide)
  have h2 : Entails.eval a c529 := h 528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8117 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8117 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1320, some c2593, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8117 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8117 : lratChecker f8117 p8117 = .success := by decide +kernel
theorem unsat8117 : Unsatisfiable (PosFin 65) f8117 := by
  apply lratCheckerSound f8117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8117
  · intro a ha; simp [p8117] at ha; subst a; trivial
  · exact checked8117
theorem derived8117 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8117 := by
  apply localUnsat_implies_entails f8117 [c1320, c2593] c8117 unsat8117 (by rfl) a
  have h0 : Entails.eval a c1320 := h 1319 (by decide)
  have h1 : Entails.eval a c2593 := h 2592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8118 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8118 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8114, some c8116, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8118 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8118 : lratChecker f8118 p8118 = .success := by decide +kernel
theorem unsat8118 : Unsatisfiable (PosFin 65) f8118 := by
  apply lratCheckerSound f8118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8118
  · intro a ha; simp [p8118] at ha; subst a; trivial
  · exact checked8118
theorem derived8118 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8118 := by
  apply localUnsat_implies_entails f8118 [c8114, c8116] c8118 unsat8118 (by rfl) a
  have h0 : Entails.eval a c8114 := derived8114 a h
  have h1 : Entails.eval a c8116 := derived8116 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8119 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8119 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c903, some c1330, some c7742, some c1176, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8119 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8119 : lratChecker f8119 p8119 = .success := by decide +kernel
theorem unsat8119 : Unsatisfiable (PosFin 65) f8119 := by
  apply lratCheckerSound f8119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8119
  · intro a ha; simp [p8119] at ha; subst a; trivial
  · exact checked8119
theorem derived8119 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8119 := by
  apply localUnsat_implies_entails f8119 [c903, c1330, c7742, c1176] c8119 unsat8119 (by rfl) a
  have h0 : Entails.eval a c903 := h 902 (by decide)
  have h1 : Entails.eval a c1330 := h 1329 (by decide)
  have h2 : Entails.eval a c7742 := derived7742 a h
  have h3 : Entails.eval a c1176 := h 1175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8120 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8120 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2587, some c499, some c1832, some c1631, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8120 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8120 : lratChecker f8120 p8120 = .success := by decide +kernel
theorem unsat8120 : Unsatisfiable (PosFin 65) f8120 := by
  apply lratCheckerSound f8120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8120
  · intro a ha; simp [p8120] at ha; subst a; trivial
  · exact checked8120
theorem derived8120 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8120 := by
  apply localUnsat_implies_entails f8120 [c2587, c499, c1832, c1631] c8120 unsat8120 (by rfl) a
  have h0 : Entails.eval a c2587 := h 2586 (by decide)
  have h1 : Entails.eval a c499 := h 498 (by decide)
  have h2 : Entails.eval a c1832 := h 1831 (by decide)
  have h3 : Entails.eval a c1631 := h 1630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8121 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8121 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8110, some c8102, some c8113, some c8117, some c8118, some c8112, some c8119, some c8120, some c568, some c593, some c2566, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8121 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8121 : lratChecker f8121 p8121 = .success := by decide +kernel
theorem unsat8121 : Unsatisfiable (PosFin 65) f8121 := by
  apply lratCheckerSound f8121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8121
  · intro a ha; simp [p8121] at ha; subst a; trivial
  · exact checked8121
theorem derived8121 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8121 := by
  apply localUnsat_implies_entails f8121 [c8110, c8102, c8113, c8117, c8118, c8112, c8119, c8120, c568, c593, c2566] c8121 unsat8121 (by rfl) a
  have h0 : Entails.eval a c8110 := derived8110 a h
  have h1 : Entails.eval a c8102 := derived8102 a h
  have h2 : Entails.eval a c8113 := derived8113 a h
  have h3 : Entails.eval a c8117 := derived8117 a h
  have h4 : Entails.eval a c8118 := derived8118 a h
  have h5 : Entails.eval a c8112 := derived8112 a h
  have h6 : Entails.eval a c8119 := derived8119 a h
  have h7 : Entails.eval a c8120 := derived8120 a h
  have h8 : Entails.eval a c568 := h 567 (by decide)
  have h9 : Entails.eval a c593 := h 592 (by decide)
  have h10 : Entails.eval a c2566 := h 2565 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8122 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8122 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2187, some c8009, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8122 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8122 : lratChecker f8122 p8122 = .success := by decide +kernel
theorem unsat8122 : Unsatisfiable (PosFin 65) f8122 := by
  apply lratCheckerSound f8122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8122
  · intro a ha; simp [p8122] at ha; subst a; trivial
  · exact checked8122
theorem derived8122 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8122 := by
  apply localUnsat_implies_entails f8122 [c2187, c8009] c8122 unsat8122 (by rfl) a
  have h0 : Entails.eval a c2187 := h 2186 (by decide)
  have h1 : Entails.eval a c8009 := derived8009 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8123 : DefaultClause 65 := directClause [(⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8123 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8110, some c8121, some c8122, some c8098, some c2345, some c2332, some c2333, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8123 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8123 : lratChecker f8123 p8123 = .success := by decide +kernel
theorem unsat8123 : Unsatisfiable (PosFin 65) f8123 := by
  apply lratCheckerSound f8123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8123
  · intro a ha; simp [p8123] at ha; subst a; trivial
  · exact checked8123
theorem derived8123 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8123 := by
  apply localUnsat_implies_entails f8123 [c8110, c8121, c8122, c8098, c2345, c2332, c2333] c8123 unsat8123 (by rfl) a
  have h0 : Entails.eval a c8110 := derived8110 a h
  have h1 : Entails.eval a c8121 := derived8121 a h
  have h2 : Entails.eval a c8122 := derived8122 a h
  have h3 : Entails.eval a c8098 := derived8098 a h
  have h4 : Entails.eval a c2345 := h 2344 (by decide)
  have h5 : Entails.eval a c2332 := h 2331 (by decide)
  have h6 : Entails.eval a c2333 := h 2332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8124 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8124 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c858, some c8052, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8124 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8124 : lratChecker f8124 p8124 = .success := by decide +kernel
theorem unsat8124 : Unsatisfiable (PosFin 65) f8124 := by
  apply lratCheckerSound f8124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8124
  · intro a ha; simp [p8124] at ha; subst a; trivial
  · exact checked8124
theorem derived8124 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8124 := by
  apply localUnsat_implies_entails f8124 [c858, c8052] c8124 unsat8124 (by rfl) a
  have h0 : Entails.eval a c858 := h 857 (by decide)
  have h1 : Entails.eval a c8052 := derived8052 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8125 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8125 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8124, some c2426, some c626, some c643, some c624, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8125 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8125 : lratChecker f8125 p8125 = .success := by decide +kernel
theorem unsat8125 : Unsatisfiable (PosFin 65) f8125 := by
  apply lratCheckerSound f8125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8125
  · intro a ha; simp [p8125] at ha; subst a; trivial
  · exact checked8125
theorem derived8125 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8125 := by
  apply localUnsat_implies_entails f8125 [c8123, c8124, c2426, c626, c643, c624] c8125 unsat8125 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c2426 := h 2425 (by decide)
  have h3 : Entails.eval a c626 := h 625 (by decide)
  have h4 : Entails.eval a c643 := h 642 (by decide)
  have h5 : Entails.eval a c624 := h 623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8126 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8126 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c638, some c630, some c639, some c627, some c611, some c612, some c6696, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8126 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8126 : lratChecker f8126 p8126 = .success := by decide +kernel
theorem unsat8126 : Unsatisfiable (PosFin 65) f8126 := by
  apply lratCheckerSound f8126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8126
  · intro a ha; simp [p8126] at ha; subst a; trivial
  · exact checked8126
theorem derived8126 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8126 := by
  apply localUnsat_implies_entails f8126 [c638, c630, c639, c627, c611, c612, c6696] c8126 unsat8126 (by rfl) a
  have h0 : Entails.eval a c638 := h 637 (by decide)
  have h1 : Entails.eval a c630 := h 629 (by decide)
  have h2 : Entails.eval a c639 := h 638 (by decide)
  have h3 : Entails.eval a c627 := h 626 (by decide)
  have h4 : Entails.eval a c611 := h 610 (by decide)
  have h5 : Entails.eval a c612 := h 611 (by decide)
  have h6 : Entails.eval a c6696 := derived6696 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8127 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8127 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8125, some c8123, some c8124, some c8126, some c2446, some c2448, some c2432, some c2421, some c2415, some c2414, some c6728, some c6746, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8127 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked8127 : lratChecker f8127 p8127 = .success := by decide +kernel
theorem unsat8127 : Unsatisfiable (PosFin 65) f8127 := by
  apply lratCheckerSound f8127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8127
  · intro a ha; simp [p8127] at ha; subst a; trivial
  · exact checked8127
theorem derived8127 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8127 := by
  apply localUnsat_implies_entails f8127 [c8125, c8123, c8124, c8126, c2446, c2448, c2432, c2421, c2415, c2414, c6728, c6746] c8127 unsat8127 (by rfl) a
  have h0 : Entails.eval a c8125 := derived8125 a h
  have h1 : Entails.eval a c8123 := derived8123 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8126 := derived8126 a h
  have h4 : Entails.eval a c2446 := h 2445 (by decide)
  have h5 : Entails.eval a c2448 := h 2447 (by decide)
  have h6 : Entails.eval a c2432 := h 2431 (by decide)
  have h7 : Entails.eval a c2421 := h 2420 (by decide)
  have h8 : Entails.eval a c2415 := h 2414 (by decide)
  have h9 : Entails.eval a c2414 := h 2413 (by decide)
  have h10 : Entails.eval a c6728 := derived6728 a h
  have h11 : Entails.eval a c6746 := derived6746 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8128 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8128 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c638, some c630, some c639, some c628, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8128 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8128 : lratChecker f8128 p8128 = .success := by decide +kernel
theorem unsat8128 : Unsatisfiable (PosFin 65) f8128 := by
  apply lratCheckerSound f8128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8128
  · intro a ha; simp [p8128] at ha; subst a; trivial
  · exact checked8128
theorem derived8128 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8128 := by
  apply localUnsat_implies_entails f8128 [c638, c630, c639, c628] c8128 unsat8128 (by rfl) a
  have h0 : Entails.eval a c638 := h 637 (by decide)
  have h1 : Entails.eval a c630 := h 629 (by decide)
  have h2 : Entails.eval a c639 := h 638 (by decide)
  have h3 : Entails.eval a c628 := h 627 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8129 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8129 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8124, some c8125, some c8127, some c8128, some c2446, some c2448, some c2447, some c2432, some c2440, some c2429, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8129 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8129 : lratChecker f8129 p8129 = .success := by decide +kernel
theorem unsat8129 : Unsatisfiable (PosFin 65) f8129 := by
  apply lratCheckerSound f8129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8129
  · intro a ha; simp [p8129] at ha; subst a; trivial
  · exact checked8129
theorem derived8129 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8129 := by
  apply localUnsat_implies_entails f8129 [c8123, c8124, c8125, c8127, c8128, c2446, c2448, c2447, c2432, c2440, c2429] c8129 unsat8129 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c8125 := derived8125 a h
  have h3 : Entails.eval a c8127 := derived8127 a h
  have h4 : Entails.eval a c8128 := derived8128 a h
  have h5 : Entails.eval a c2446 := h 2445 (by decide)
  have h6 : Entails.eval a c2448 := h 2447 (by decide)
  have h7 : Entails.eval a c2447 := h 2446 (by decide)
  have h8 : Entails.eval a c2432 := h 2431 (by decide)
  have h9 : Entails.eval a c2440 := h 2439 (by decide)
  have h10 : Entails.eval a c2429 := h 2428 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8130 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8130 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8106, some c553, some c507, some c1826, some c2615, some c1643, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8130 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8130 : lratChecker f8130 p8130 = .success := by decide +kernel
theorem unsat8130 : Unsatisfiable (PosFin 65) f8130 := by
  apply lratCheckerSound f8130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8130
  · intro a ha; simp [p8130] at ha; subst a; trivial
  · exact checked8130
theorem derived8130 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8130 := by
  apply localUnsat_implies_entails f8130 [c8123, c8106, c553, c507, c1826, c2615, c1643] c8130 unsat8130 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8106 := derived8106 a h
  have h2 : Entails.eval a c553 := h 552 (by decide)
  have h3 : Entails.eval a c507 := h 506 (by decide)
  have h4 : Entails.eval a c1826 := h 1825 (by decide)
  have h5 : Entails.eval a c2615 := h 2614 (by decide)
  have h6 : Entails.eval a c1643 := h 1642 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8131 : DefaultClause 65 := directClause [(⟨9, by decide⟩, true), (⟨31, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8131 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1316, some c1306, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8131 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8131 : lratChecker f8131 p8131 = .success := by decide +kernel
theorem unsat8131 : Unsatisfiable (PosFin 65) f8131 := by
  apply lratCheckerSound f8131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8131
  · intro a ha; simp [p8131] at ha; subst a; trivial
  · exact checked8131
theorem derived8131 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8131 := by
  apply localUnsat_implies_entails f8131 [c1316, c1306] c8131 unsat8131 (by rfl) a
  have h0 : Entails.eval a c1316 := h 1315 (by decide)
  have h1 : Entails.eval a c1306 := h 1305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8132 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8132 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8130, some c8087, some c8107, some c8131, some c2591, some c2584, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8132 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8132 : lratChecker f8132 p8132 = .success := by decide +kernel
theorem unsat8132 : Unsatisfiable (PosFin 65) f8132 := by
  apply lratCheckerSound f8132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8132
  · intro a ha; simp [p8132] at ha; subst a; trivial
  · exact checked8132
theorem derived8132 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8132 := by
  apply localUnsat_implies_entails f8132 [c8130, c8087, c8107, c8131, c2591, c2584] c8132 unsat8132 (by rfl) a
  have h0 : Entails.eval a c8130 := derived8130 a h
  have h1 : Entails.eval a c8087 := derived8087 a h
  have h2 : Entails.eval a c8107 := derived8107 a h
  have h3 : Entails.eval a c8131 := derived8131 a h
  have h4 : Entails.eval a c2591 := h 2590 (by decide)
  have h5 : Entails.eval a c2584 := h 2583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8133 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8133 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8129, some c8132, some c2320, some c2339, some c2340, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8133 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked8133 : lratChecker f8133 p8133 = .success := by decide +kernel
theorem unsat8133 : Unsatisfiable (PosFin 65) f8133 := by
  apply lratCheckerSound f8133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8133
  · intro a ha; simp [p8133] at ha; subst a; trivial
  · exact checked8133
theorem derived8133 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8133 := by
  apply localUnsat_implies_entails f8133 [c8123, c8129, c8132, c2320, c2339, c2340] c8133 unsat8133 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8129 := derived8129 a h
  have h2 : Entails.eval a c8132 := derived8132 a h
  have h3 : Entails.eval a c2320 := h 2319 (by decide)
  have h4 : Entails.eval a c2339 := h 2338 (by decide)
  have h5 : Entails.eval a c2340 := h 2339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8134 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8134 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c642, some c624, some c626, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8134 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8134 : lratChecker f8134 p8134 = .success := by decide +kernel
theorem unsat8134 : Unsatisfiable (PosFin 65) f8134 := by
  apply lratCheckerSound f8134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8134
  · intro a ha; simp [p8134] at ha; subst a; trivial
  · exact checked8134
theorem derived8134 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8134 := by
  apply localUnsat_implies_entails f8134 [c642, c624, c626] c8134 unsat8134 (by rfl) a
  have h0 : Entails.eval a c642 := h 641 (by decide)
  have h1 : Entails.eval a c624 := h 623 (by decide)
  have h2 : Entails.eval a c626 := h 625 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8135 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8135 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8124, some c8034, some c1529, some c8037, some c1522, some c1517, some c1526, some c1530, some c7973, some c2434, some c2419, some c1519, some c8070, some c452, some c2156, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8135 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked8135 : lratChecker f8135 p8135 = .success := by decide +kernel
theorem unsat8135 : Unsatisfiable (PosFin 65) f8135 := by
  apply lratCheckerSound f8135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8135
  · intro a ha; simp [p8135] at ha; subst a; trivial
  · exact checked8135
theorem derived8135 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8135 := by
  apply localUnsat_implies_entails f8135 [c8124, c8034, c1529, c8037, c1522, c1517, c1526, c1530, c7973, c2434, c2419, c1519, c8070, c452, c2156] c8135 unsat8135 (by rfl) a
  have h0 : Entails.eval a c8124 := derived8124 a h
  have h1 : Entails.eval a c8034 := derived8034 a h
  have h2 : Entails.eval a c1529 := h 1528 (by decide)
  have h3 : Entails.eval a c8037 := derived8037 a h
  have h4 : Entails.eval a c1522 := h 1521 (by decide)
  have h5 : Entails.eval a c1517 := h 1516 (by decide)
  have h6 : Entails.eval a c1526 := h 1525 (by decide)
  have h7 : Entails.eval a c1530 := h 1529 (by decide)
  have h8 : Entails.eval a c7973 := derived7973 a h
  have h9 : Entails.eval a c2434 := h 2433 (by decide)
  have h10 : Entails.eval a c2419 := h 2418 (by decide)
  have h11 : Entails.eval a c1519 := h 1518 (by decide)
  have h12 : Entails.eval a c8070 := derived8070 a h
  have h13 : Entails.eval a c452 := h 451 (by decide)
  have h14 : Entails.eval a c2156 := h 2155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8136 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8136 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8124, some c8134, some c2437, some c8135, some c8054, some c8066, some c8072, some c2134, some c8067, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8136 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8136 : lratChecker f8136 p8136 = .success := by decide +kernel
theorem unsat8136 : Unsatisfiable (PosFin 65) f8136 := by
  apply lratCheckerSound f8136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8136
  · intro a ha; simp [p8136] at ha; subst a; trivial
  · exact checked8136
theorem derived8136 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8136 := by
  apply localUnsat_implies_entails f8136 [c8123, c8124, c8134, c2437, c8135, c8054, c8066, c8072, c2134, c8067] c8136 unsat8136 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c8134 := derived8134 a h
  have h3 : Entails.eval a c2437 := h 2436 (by decide)
  have h4 : Entails.eval a c8135 := derived8135 a h
  have h5 : Entails.eval a c8054 := derived8054 a h
  have h6 : Entails.eval a c8066 := derived8066 a h
  have h7 : Entails.eval a c8072 := derived8072 a h
  have h8 : Entails.eval a c2134 := h 2133 (by decide)
  have h9 : Entails.eval a c8067 := derived8067 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8137 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8137 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8124, some c8134, some c2446, some c2437, some c2419, some c8136, some c2449, some c2440, some c2444, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8137 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8137 : lratChecker f8137 p8137 = .success := by decide +kernel
theorem unsat8137 : Unsatisfiable (PosFin 65) f8137 := by
  apply lratCheckerSound f8137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8137
  · intro a ha; simp [p8137] at ha; subst a; trivial
  · exact checked8137
theorem derived8137 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8137 := by
  apply localUnsat_implies_entails f8137 [c8123, c8124, c8134, c2446, c2437, c2419, c8136, c2449, c2440, c2444] c8137 unsat8137 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c8134 := derived8134 a h
  have h3 : Entails.eval a c2446 := h 2445 (by decide)
  have h4 : Entails.eval a c2437 := h 2436 (by decide)
  have h5 : Entails.eval a c2419 := h 2418 (by decide)
  have h6 : Entails.eval a c8136 := derived8136 a h
  have h7 : Entails.eval a c2449 := h 2448 (by decide)
  have h8 : Entails.eval a c2440 := h 2439 (by decide)
  have h9 : Entails.eval a c2444 := h 2443 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8138 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8138 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8124, some c8133, some c8126, some c2417, some c2446, some c2448, some c2432, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8138 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8138 : lratChecker f8138 p8138 = .success := by decide +kernel
theorem unsat8138 : Unsatisfiable (PosFin 65) f8138 := by
  apply lratCheckerSound f8138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8138
  · intro a ha; simp [p8138] at ha; subst a; trivial
  · exact checked8138
theorem derived8138 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8138 := by
  apply localUnsat_implies_entails f8138 [c8123, c8124, c8133, c8126, c2417, c2446, c2448, c2432] c8138 unsat8138 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c8133 := derived8133 a h
  have h3 : Entails.eval a c8126 := derived8126 a h
  have h4 : Entails.eval a c2417 := h 2416 (by decide)
  have h5 : Entails.eval a c2446 := h 2445 (by decide)
  have h6 : Entails.eval a c2448 := h 2447 (by decide)
  have h7 : Entails.eval a c2432 := h 2431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8139 : DefaultClause 65 := directClause [(⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8139 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8124, some c8133, some c8138, some c8128, some c8055, some c2446, some c2448, some c2432, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8139 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8139 : lratChecker f8139 p8139 = .success := by decide +kernel
theorem unsat8139 : Unsatisfiable (PosFin 65) f8139 := by
  apply lratCheckerSound f8139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8139
  · intro a ha; simp [p8139] at ha; subst a; trivial
  · exact checked8139
theorem derived8139 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8139 := by
  apply localUnsat_implies_entails f8139 [c8123, c8124, c8133, c8138, c8128, c8055, c2446, c2448, c2432] c8139 unsat8139 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8124 := derived8124 a h
  have h2 : Entails.eval a c8133 := derived8133 a h
  have h3 : Entails.eval a c8138 := derived8138 a h
  have h4 : Entails.eval a c8128 := derived8128 a h
  have h5 : Entails.eval a c8055 := derived8055 a h
  have h6 : Entails.eval a c2446 := h 2445 (by decide)
  have h7 : Entails.eval a c2448 := h 2447 (by decide)
  have h8 : Entails.eval a c2432 := h 2431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8140 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨14, by decide⟩, true), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8140 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1901, some c452, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8140 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8140 : lratChecker f8140 p8140 = .success := by decide +kernel
theorem unsat8140 : Unsatisfiable (PosFin 65) f8140 := by
  apply lratCheckerSound f8140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8140
  · intro a ha; simp [p8140] at ha; subst a; trivial
  · exact checked8140
theorem derived8140 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8140 := by
  apply localUnsat_implies_entails f8140 [c1901, c452] c8140 unsat8140 (by rfl) a
  have h0 : Entails.eval a c1901 := h 1900 (by decide)
  have h1 : Entails.eval a c452 := h 451 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8141 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨14, by decide⟩, true), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8141 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c2183, some c8140, some c1894, some c433, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8141 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8141 : lratChecker f8141 p8141 = .success := by decide +kernel
theorem unsat8141 : Unsatisfiable (PosFin 65) f8141 := by
  apply lratCheckerSound f8141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8141
  · intro a ha; simp [p8141] at ha; subst a; trivial
  · exact checked8141
theorem derived8141 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8141 := by
  apply localUnsat_implies_entails f8141 [c8123, c2183, c8140, c1894, c433] c8141 unsat8141 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c2183 := h 2182 (by decide)
  have h2 : Entails.eval a c8140 := derived8140 a h
  have h3 : Entails.eval a c1894 := h 1893 (by decide)
  have h4 : Entails.eval a c433 := h 432 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8142 : DefaultClause 65 := directClause [(⟨14, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8142 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8133, some c8123, some c8124, some c8139, some c8134, some c8137, some c2446, some c2202, some c2195, some c8141, some c2449, some c2204, some c2444, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8142 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8142 : lratChecker f8142 p8142 = .success := by decide +kernel
theorem unsat8142 : Unsatisfiable (PosFin 65) f8142 := by
  apply lratCheckerSound f8142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8142
  · intro a ha; simp [p8142] at ha; subst a; trivial
  · exact checked8142
theorem derived8142 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8142 := by
  apply localUnsat_implies_entails f8142 [c8133, c8123, c8124, c8139, c8134, c8137, c2446, c2202, c2195, c8141, c2449, c2204, c2444] c8142 unsat8142 (by rfl) a
  have h0 : Entails.eval a c8133 := derived8133 a h
  have h1 : Entails.eval a c8123 := derived8123 a h
  have h2 : Entails.eval a c8124 := derived8124 a h
  have h3 : Entails.eval a c8139 := derived8139 a h
  have h4 : Entails.eval a c8134 := derived8134 a h
  have h5 : Entails.eval a c8137 := derived8137 a h
  have h6 : Entails.eval a c2446 := h 2445 (by decide)
  have h7 : Entails.eval a c2202 := h 2201 (by decide)
  have h8 : Entails.eval a c2195 := h 2194 (by decide)
  have h9 : Entails.eval a c8141 := derived8141 a h
  have h10 : Entails.eval a c2449 := h 2448 (by decide)
  have h11 : Entails.eval a c2204 := h 2203 (by decide)
  have h12 : Entails.eval a c2444 := h 2443 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8143 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8143 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c545, some c553, some c533, some c507, some c1826, some c2615, some c1630, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8143 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8143 : lratChecker f8143 p8143 = .success := by decide +kernel
theorem unsat8143 : Unsatisfiable (PosFin 65) f8143 := by
  apply lratCheckerSound f8143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8143
  · intro a ha; simp [p8143] at ha; subst a; trivial
  · exact checked8143
theorem derived8143 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8143 := by
  apply localUnsat_implies_entails f8143 [c545, c553, c533, c507, c1826, c2615, c1630] c8143 unsat8143 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c553 := h 552 (by decide)
  have h2 : Entails.eval a c533 := h 532 (by decide)
  have h3 : Entails.eval a c507 := h 506 (by decide)
  have h4 : Entails.eval a c1826 := h 1825 (by decide)
  have h5 : Entails.eval a c2615 := h 2614 (by decide)
  have h6 : Entails.eval a c1630 := h 1629 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8144 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8144 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7719, some c39, some c40, some c6707, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8144 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8144 : lratChecker f8144 p8144 = .success := by decide +kernel
theorem unsat8144 : Unsatisfiable (PosFin 65) f8144 := by
  apply lratCheckerSound f8144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8144
  · intro a ha; simp [p8144] at ha; subst a; trivial
  · exact checked8144
theorem derived8144 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8144 := by
  apply localUnsat_implies_entails f8144 [c7719, c39, c40, c6707] c8144 unsat8144 (by rfl) a
  have h0 : Entails.eval a c7719 := derived7719 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c6707 := derived6707 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8145 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8145 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8081, some c8123, some c8133, some c8142, some c8143, some c1492, some c1485, some c8037, some c1517, some c7973, some c8144, some c570, some c2559, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8145 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked8145 : lratChecker f8145 p8145 = .success := by decide +kernel
theorem unsat8145 : Unsatisfiable (PosFin 65) f8145 := by
  apply lratCheckerSound f8145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8145
  · intro a ha; simp [p8145] at ha; subst a; trivial
  · exact checked8145
theorem derived8145 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8145 := by
  apply localUnsat_implies_entails f8145 [c7849, c8081, c8123, c8133, c8142, c8143, c1492, c1485, c8037, c1517, c7973, c8144, c570, c2559] c8145 unsat8145 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8081 := derived8081 a h
  have h2 : Entails.eval a c8123 := derived8123 a h
  have h3 : Entails.eval a c8133 := derived8133 a h
  have h4 : Entails.eval a c8142 := derived8142 a h
  have h5 : Entails.eval a c8143 := derived8143 a h
  have h6 : Entails.eval a c1492 := h 1491 (by decide)
  have h7 : Entails.eval a c1485 := h 1484 (by decide)
  have h8 : Entails.eval a c8037 := derived8037 a h
  have h9 : Entails.eval a c1517 := h 1516 (by decide)
  have h10 : Entails.eval a c7973 := derived7973 a h
  have h11 : Entails.eval a c8144 := derived8144 a h
  have h12 : Entails.eval a c570 := h 569 (by decide)
  have h13 : Entails.eval a c2559 := h 2558 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8146 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8146 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8081, some c8123, some c8133, some c8142, some c8143, some c8145, some c8058, some c8079, some c8066, some c1344, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8146 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8146 : lratChecker f8146 p8146 = .success := by decide +kernel
theorem unsat8146 : Unsatisfiable (PosFin 65) f8146 := by
  apply lratCheckerSound f8146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8146
  · intro a ha; simp [p8146] at ha; subst a; trivial
  · exact checked8146
theorem derived8146 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8146 := by
  apply localUnsat_implies_entails f8146 [c7849, c8081, c8123, c8133, c8142, c8143, c8145, c8058, c8079, c8066, c1344] c8146 unsat8146 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8081 := derived8081 a h
  have h2 : Entails.eval a c8123 := derived8123 a h
  have h3 : Entails.eval a c8133 := derived8133 a h
  have h4 : Entails.eval a c8142 := derived8142 a h
  have h5 : Entails.eval a c8143 := derived8143 a h
  have h6 : Entails.eval a c8145 := derived8145 a h
  have h7 : Entails.eval a c8058 := derived8058 a h
  have h8 : Entails.eval a c8079 := derived8079 a h
  have h9 : Entails.eval a c8066 := derived8066 a h
  have h10 : Entails.eval a c1344 := h 1343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8147 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8147 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8081, some c8123, some c8133, some c8142, some c8143, some c8146, some c2437, some c2417, some c2432, some c8144, some c7618, some c8079, some c1329, some c1819, some c1098, some c1630, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8147 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8147 : lratChecker f8147 p8147 = .success := by decide +kernel
theorem unsat8147 : Unsatisfiable (PosFin 65) f8147 := by
  apply lratCheckerSound f8147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8147
  · intro a ha; simp [p8147] at ha; subst a; trivial
  · exact checked8147
theorem derived8147 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8147 := by
  apply localUnsat_implies_entails f8147 [c7849, c8081, c8123, c8133, c8142, c8143, c8146, c2437, c2417, c2432, c8144, c7618, c8079, c1329, c1819, c1098, c1630] c8147 unsat8147 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8081 := derived8081 a h
  have h2 : Entails.eval a c8123 := derived8123 a h
  have h3 : Entails.eval a c8133 := derived8133 a h
  have h4 : Entails.eval a c8142 := derived8142 a h
  have h5 : Entails.eval a c8143 := derived8143 a h
  have h6 : Entails.eval a c8146 := derived8146 a h
  have h7 : Entails.eval a c2437 := h 2436 (by decide)
  have h8 : Entails.eval a c2417 := h 2416 (by decide)
  have h9 : Entails.eval a c2432 := h 2431 (by decide)
  have h10 : Entails.eval a c8144 := derived8144 a h
  have h11 : Entails.eval a c7618 := derived7618 a h
  have h12 : Entails.eval a c8079 := derived8079 a h
  have h13 : Entails.eval a c1329 := h 1328 (by decide)
  have h14 : Entails.eval a c1819 := h 1818 (by decide)
  have h15 : Entails.eval a c1098 := h 1097 (by decide)
  have h16 : Entails.eval a c1630 := h 1629 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8148 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8148 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8034, some c8037, some c1517, some c1494, some c1526, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8148 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked8148 : lratChecker f8148 p8148 = .success := by decide +kernel
theorem unsat8148 : Unsatisfiable (PosFin 65) f8148 := by
  apply lratCheckerSound f8148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8148
  · intro a ha; simp [p8148] at ha; subst a; trivial
  · exact checked8148
theorem derived8148 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8148 := by
  apply localUnsat_implies_entails f8148 [c8034, c8037, c1517, c1494, c1526] c8148 unsat8148 (by rfl) a
  have h0 : Entails.eval a c8034 := derived8034 a h
  have h1 : Entails.eval a c8037 := derived8037 a h
  have h2 : Entails.eval a c1517 := h 1516 (by decide)
  have h3 : Entails.eval a c1494 := h 1493 (by decide)
  have h4 : Entails.eval a c1526 := h 1525 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c8149 : DefaultClause 65 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨14, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8149 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c576, some c2569, some c1376, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8149 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8149 : lratChecker f8149 p8149 = .success := by decide +kernel
theorem unsat8149 : Unsatisfiable (PosFin 65) f8149 := by
  apply lratCheckerSound f8149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8149
  · intro a ha; simp [p8149] at ha; subst a; trivial
  · exact checked8149
theorem derived8149 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8149 := by
  apply localUnsat_implies_entails f8149 [c576, c2569, c1376] c8149 unsat8149 (by rfl) a
  have h0 : Entails.eval a c576 := h 575 (by decide)
  have h1 : Entails.eval a c2569 := h 2568 (by decide)
  have h2 : Entails.eval a c1376 := h 1375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8150 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8150 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c594, some c2608, some c1831, some c1630, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8150 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8150 : lratChecker f8150 p8150 = .success := by decide +kernel
theorem unsat8150 : Unsatisfiable (PosFin 65) f8150 := by
  apply lratCheckerSound f8150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8150
  · intro a ha; simp [p8150] at ha; subst a; trivial
  · exact checked8150
theorem derived8150 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8150 := by
  apply localUnsat_implies_entails f8150 [c594, c2608, c1831, c1630] c8150 unsat8150 (by rfl) a
  have h0 : Entails.eval a c594 := h 593 (by decide)
  have h1 : Entails.eval a c2608 := h 2607 (by decide)
  have h2 : Entails.eval a c1831 := h 1830 (by decide)
  have h3 : Entails.eval a c1630 := h 1629 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8151 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8151 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1335, some c1313, some c2614, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p8151 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8151 : lratChecker f8151 p8151 = .success := by decide +kernel
theorem unsat8151 : Unsatisfiable (PosFin 65) f8151 := by
  apply lratCheckerSound f8151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8151
  · intro a ha; simp [p8151] at ha; subst a; trivial
  · exact checked8151
theorem derived8151 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8151 := by
  apply localUnsat_implies_entails f8151 [c1335, c1313, c2614] c8151 unsat8151 (by rfl) a
  have h0 : Entails.eval a c1335 := h 1334 (by decide)
  have h1 : Entails.eval a c1313 := h 1312 (by decide)
  have h2 : Entails.eval a c2614 := h 2613 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8152 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8152 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c568, some c593, some c2566, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8152 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8152 : lratChecker f8152 p8152 = .success := by decide +kernel
theorem unsat8152 : Unsatisfiable (PosFin 65) f8152 := by
  apply lratCheckerSound f8152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8152
  · intro a ha; simp [p8152] at ha; subst a; trivial
  · exact checked8152
theorem derived8152 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8152 := by
  apply localUnsat_implies_entails f8152 [c568, c593, c2566] c8152 unsat8152 (by rfl) a
  have h0 : Entails.eval a c568 := h 567 (by decide)
  have h1 : Entails.eval a c593 := h 592 (by decide)
  have h2 : Entails.eval a c2566 := h 2565 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8153 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8153 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8123, some c8143, some c8148, some c8152, some c8150, some c1319, some c8151, some c2581, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8153 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8153 : lratChecker f8153 p8153 = .success := by decide +kernel
theorem unsat8153 : Unsatisfiable (PosFin 65) f8153 := by
  apply lratCheckerSound f8153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8153
  · intro a ha; simp [p8153] at ha; subst a; trivial
  · exact checked8153
theorem derived8153 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8153 := by
  apply localUnsat_implies_entails f8153 [c8123, c8143, c8148, c8152, c8150, c1319, c8151, c2581] c8153 unsat8153 (by rfl) a
  have h0 : Entails.eval a c8123 := derived8123 a h
  have h1 : Entails.eval a c8143 := derived8143 a h
  have h2 : Entails.eval a c8148 := derived8148 a h
  have h3 : Entails.eval a c8152 := derived8152 a h
  have h4 : Entails.eval a c8150 := derived8150 a h
  have h5 : Entails.eval a c1319 := h 1318 (by decide)
  have h6 : Entails.eval a c8151 := derived8151 a h
  have h7 : Entails.eval a c2581 := h 2580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8154 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8154 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8081, some c8142, some c8133, some c8123, some c8143, some c8147, some c8153, some c2446, some c2449, some c8055, some c2445, some c2432, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8154 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8154 : lratChecker f8154 p8154 = .success := by decide +kernel
theorem unsat8154 : Unsatisfiable (PosFin 65) f8154 := by
  apply lratCheckerSound f8154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8154
  · intro a ha; simp [p8154] at ha; subst a; trivial
  · exact checked8154
theorem derived8154 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8154 := by
  apply localUnsat_implies_entails f8154 [c7849, c8081, c8142, c8133, c8123, c8143, c8147, c8153, c2446, c2449, c8055, c2445, c2432] c8154 unsat8154 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8081 := derived8081 a h
  have h2 : Entails.eval a c8142 := derived8142 a h
  have h3 : Entails.eval a c8133 := derived8133 a h
  have h4 : Entails.eval a c8123 := derived8123 a h
  have h5 : Entails.eval a c8143 := derived8143 a h
  have h6 : Entails.eval a c8147 := derived8147 a h
  have h7 : Entails.eval a c8153 := derived8153 a h
  have h8 : Entails.eval a c2446 := h 2445 (by decide)
  have h9 : Entails.eval a c2449 := h 2448 (by decide)
  have h10 : Entails.eval a c8055 := derived8055 a h
  have h11 : Entails.eval a c2445 := h 2444 (by decide)
  have h12 : Entails.eval a c2432 := h 2431 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8155 : DefaultClause 65 := directClause [(⟨23, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8155 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2591, some c1493, some c1316, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p8155 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8155 : lratChecker f8155 p8155 = .success := by decide +kernel
theorem unsat8155 : Unsatisfiable (PosFin 65) f8155 := by
  apply lratCheckerSound f8155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8155
  · intro a ha; simp [p8155] at ha; subst a; trivial
  · exact checked8155
theorem derived8155 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8155 := by
  apply localUnsat_implies_entails f8155 [c2591, c1493, c1316] c8155 unsat8155 (by rfl) a
  have h0 : Entails.eval a c2591 := h 2590 (by decide)
  have h1 : Entails.eval a c1493 := h 1492 (by decide)
  have h2 : Entails.eval a c1316 := h 1315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8156 : DefaultClause 65 := directClause [(⟨6, by decide⟩, true), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8156 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8081, some c8142, some c8123, some c8154, some c8155, some c1492, some c2590, some c1315, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8156 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked8156 : lratChecker f8156 p8156 = .success := by decide +kernel
theorem unsat8156 : Unsatisfiable (PosFin 65) f8156 := by
  apply lratCheckerSound f8156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8156
  · intro a ha; simp [p8156] at ha; subst a; trivial
  · exact checked8156
theorem derived8156 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8156 := by
  apply localUnsat_implies_entails f8156 [c7849, c8081, c8142, c8123, c8154, c8155, c1492, c2590, c1315] c8156 unsat8156 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8081 := derived8081 a h
  have h2 : Entails.eval a c8142 := derived8142 a h
  have h3 : Entails.eval a c8123 := derived8123 a h
  have h4 : Entails.eval a c8154 := derived8154 a h
  have h5 : Entails.eval a c8155 := derived8155 a h
  have h6 : Entails.eval a c1492 := h 1491 (by decide)
  have h7 : Entails.eval a c2590 := h 2589 (by decide)
  have h8 : Entails.eval a c1315 := h 1314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8157 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, false), (⟨16, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8157 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2260, some c687, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8157 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked8157 : lratChecker f8157 p8157 = .success := by decide +kernel
theorem unsat8157 : Unsatisfiable (PosFin 65) f8157 := by
  apply lratCheckerSound f8157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8157
  · intro a ha; simp [p8157] at ha; subst a; trivial
  · exact checked8157
theorem derived8157 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8157 := by
  apply localUnsat_implies_entails f8157 [c2260, c687] c8157 unsat8157 (by rfl) a
  have h0 : Entails.eval a c2260 := h 2259 (by decide)
  have h1 : Entails.eval a c687 := h 686 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c8158 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8158 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2398, some c2260, some c656, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8158 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8158 : lratChecker f8158 p8158 = .success := by decide +kernel
theorem unsat8158 : Unsatisfiable (PosFin 65) f8158 := by
  apply lratCheckerSound f8158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8158
  · intro a ha; simp [p8158] at ha; subst a; trivial
  · exact checked8158
theorem derived8158 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8158 := by
  apply localUnsat_implies_entails f8158 [c2398, c2260, c656] c8158 unsat8158 (by rfl) a
  have h0 : Entails.eval a c2398 := h 2397 (by decide)
  have h1 : Entails.eval a c2260 := h 2259 (by decide)
  have h2 : Entails.eval a c656 := h 655 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8159 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8159 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8081, some c8123, some c8133, some c8142, some c8156, some c2339, some c2337, some c2340, some c2328, some c2327, some c2334, some c2314, some c8158, some c2379, some c2264, some c658, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8159 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8159 : lratChecker f8159 p8159 = .success := by decide +kernel
theorem unsat8159 : Unsatisfiable (PosFin 65) f8159 := by
  apply lratCheckerSound f8159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8159
  · intro a ha; simp [p8159] at ha; subst a; trivial
  · exact checked8159
theorem derived8159 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8159 := by
  apply localUnsat_implies_entails f8159 [c7849, c8081, c8123, c8133, c8142, c8156, c2339, c2337, c2340, c2328, c2327, c2334, c2314, c8158, c2379, c2264, c658] c8159 unsat8159 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8081 := derived8081 a h
  have h2 : Entails.eval a c8123 := derived8123 a h
  have h3 : Entails.eval a c8133 := derived8133 a h
  have h4 : Entails.eval a c8142 := derived8142 a h
  have h5 : Entails.eval a c8156 := derived8156 a h
  have h6 : Entails.eval a c2339 := h 2338 (by decide)
  have h7 : Entails.eval a c2337 := h 2336 (by decide)
  have h8 : Entails.eval a c2340 := h 2339 (by decide)
  have h9 : Entails.eval a c2328 := h 2327 (by decide)
  have h10 : Entails.eval a c2327 := h 2326 (by decide)
  have h11 : Entails.eval a c2334 := h 2333 (by decide)
  have h12 : Entails.eval a c2314 := h 2313 (by decide)
  have h13 : Entails.eval a c8158 := derived8158 a h
  have h14 : Entails.eval a c2379 := h 2378 (by decide)
  have h15 : Entails.eval a c2264 := h 2263 (by decide)
  have h16 : Entails.eval a c658 := h 657 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8160 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8160 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c7849, some c847, some c863, some c8116, some c551, some c541, some c543, some c520, some c857, some c7941, some c7604, some c7766, some c2672, some c1196, some c941, some c2637, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8160 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked8160 : lratChecker f8160 p8160 = .success := by decide +kernel
theorem unsat8160 : Unsatisfiable (PosFin 65) f8160 := by
  apply lratCheckerSound f8160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8160
  · intro a ha; simp [p8160] at ha; subst a; trivial
  · exact checked8160
theorem derived8160 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8160 := by
  apply localUnsat_implies_entails f8160 [c8159, c7849, c847, c863, c8116, c551, c541, c543, c520, c857, c7941, c7604, c7766, c2672, c1196, c941, c2637] c8160 unsat8160 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c847 := h 846 (by decide)
  have h3 : Entails.eval a c863 := h 862 (by decide)
  have h4 : Entails.eval a c8116 := derived8116 a h
  have h5 : Entails.eval a c551 := h 550 (by decide)
  have h6 : Entails.eval a c541 := h 540 (by decide)
  have h7 : Entails.eval a c543 := h 542 (by decide)
  have h8 : Entails.eval a c520 := h 519 (by decide)
  have h9 : Entails.eval a c857 := h 856 (by decide)
  have h10 : Entails.eval a c7941 := derived7941 a h
  have h11 : Entails.eval a c7604 := derived7604 a h
  have h12 : Entails.eval a c7766 := derived7766 a h
  have h13 : Entails.eval a c2672 := h 2671 (by decide)
  have h14 : Entails.eval a c1196 := h 1195 (by decide)
  have h15 : Entails.eval a c941 := h 940 (by decide)
  have h16 : Entails.eval a c2637 := h 2636 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8161 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8161 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1542, some c1260, some c1654, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8161 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8161 : lratChecker f8161 p8161 = .success := by decide +kernel
theorem unsat8161 : Unsatisfiable (PosFin 65) f8161 := by
  apply lratCheckerSound f8161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8161
  · intro a ha; simp [p8161] at ha; subst a; trivial
  · exact checked8161
theorem derived8161 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8161 := by
  apply localUnsat_implies_entails f8161 [c1542, c1260, c1654] c8161 unsat8161 (by rfl) a
  have h0 : Entails.eval a c1542 := h 1541 (by decide)
  have h1 : Entails.eval a c1260 := h 1259 (by decide)
  have h2 : Entails.eval a c1654 := h 1653 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8162 : DefaultClause 65 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8162 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8161, some c8011, some c8104, some c2470, some c626, some c2463, some c623, some c1200, some c2108, some c2084, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8162 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8162 : lratChecker f8162 p8162 = .success := by decide +kernel
theorem unsat8162 : Unsatisfiable (PosFin 65) f8162 := by
  apply lratCheckerSound f8162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8162
  · intro a ha; simp [p8162] at ha; subst a; trivial
  · exact checked8162
theorem derived8162 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8162 := by
  apply localUnsat_implies_entails f8162 [c8161, c8011, c8104, c2470, c626, c2463, c623, c1200, c2108, c2084] c8162 unsat8162 (by rfl) a
  have h0 : Entails.eval a c8161 := derived8161 a h
  have h1 : Entails.eval a c8011 := derived8011 a h
  have h2 : Entails.eval a c8104 := derived8104 a h
  have h3 : Entails.eval a c2470 := h 2469 (by decide)
  have h4 : Entails.eval a c626 := h 625 (by decide)
  have h5 : Entails.eval a c2463 := h 2462 (by decide)
  have h6 : Entails.eval a c623 := h 622 (by decide)
  have h7 : Entails.eval a c1200 := h 1199 (by decide)
  have h8 : Entails.eval a c2108 := h 2107 (by decide)
  have h9 : Entails.eval a c2084 := h 2083 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8163 : DefaultClause 65 := directClause [(⟨25, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8163 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c7766, some c1259, some c7604, some c1735, some c7419, some c7976, some c2545, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8163 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked8163 : lratChecker f8163 p8163 = .success := by decide +kernel
theorem unsat8163 : Unsatisfiable (PosFin 65) f8163 := by
  apply lratCheckerSound f8163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8163
  · intro a ha; simp [p8163] at ha; subst a; trivial
  · exact checked8163
theorem derived8163 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8163 := by
  apply localUnsat_implies_entails f8163 [c7849, c7766, c1259, c7604, c1735, c7419, c7976, c2545] c8163 unsat8163 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c7766 := derived7766 a h
  have h2 : Entails.eval a c1259 := h 1258 (by decide)
  have h3 : Entails.eval a c7604 := derived7604 a h
  have h4 : Entails.eval a c1735 := h 1734 (by decide)
  have h5 : Entails.eval a c7419 := derived7419 a h
  have h6 : Entails.eval a c7976 := derived7976 a h
  have h7 : Entails.eval a c2545 := h 2544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8164 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8164 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c636, some c637, some c641, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8164 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8164 : lratChecker f8164 p8164 = .success := by decide +kernel
theorem unsat8164 : Unsatisfiable (PosFin 65) f8164 := by
  apply lratCheckerSound f8164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8164
  · intro a ha; simp [p8164] at ha; subst a; trivial
  · exact checked8164
theorem derived8164 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8164 := by
  apply localUnsat_implies_entails f8164 [c636, c637, c641] c8164 unsat8164 (by rfl) a
  have h0 : Entails.eval a c636 := h 635 (by decide)
  have h1 : Entails.eval a c637 := h 636 (by decide)
  have h2 : Entails.eval a c641 := h 640 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8165 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨25, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8165 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8164, some c1982, some c2480, some c7929, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8165 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8165 : lratChecker f8165 p8165 = .success := by decide +kernel
theorem unsat8165 : Unsatisfiable (PosFin 65) f8165 := by
  apply lratCheckerSound f8165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8165
  · intro a ha; simp [p8165] at ha; subst a; trivial
  · exact checked8165
theorem derived8165 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8165 := by
  apply localUnsat_implies_entails f8165 [c8164, c1982, c2480, c7929] c8165 unsat8165 (by rfl) a
  have h0 : Entails.eval a c8164 := derived8164 a h
  have h1 : Entails.eval a c1982 := h 1981 (by decide)
  have h2 : Entails.eval a c2480 := h 2479 (by decide)
  have h3 : Entails.eval a c7929 := derived7929 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8166 : DefaultClause 65 := directClause [(⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8166 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1554, some c1271, some c1665, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8166 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8166 : lratChecker f8166 p8166 = .success := by decide +kernel
theorem unsat8166 : Unsatisfiable (PosFin 65) f8166 := by
  apply lratCheckerSound f8166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8166
  · intro a ha; simp [p8166] at ha; subst a; trivial
  · exact checked8166
theorem derived8166 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8166 := by
  apply localUnsat_implies_entails f8166 [c1554, c1271, c1665] c8166 unsat8166 (by rfl) a
  have h0 : Entails.eval a c1554 := h 1553 (by decide)
  have h1 : Entails.eval a c1271 := h 1270 (by decide)
  have h2 : Entails.eval a c1665 := h 1664 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8167 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8167 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8163, some c8165, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8167 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8167 : lratChecker f8167 p8167 = .success := by decide +kernel
theorem unsat8167 : Unsatisfiable (PosFin 65) f8167 := by
  apply lratCheckerSound f8167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8167
  · intro a ha; simp [p8167] at ha; subst a; trivial
  · exact checked8167
theorem derived8167 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8167 := by
  apply localUnsat_implies_entails f8167 [c7849, c8163, c8165] c8167 unsat8167 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8163 := derived8163 a h
  have h2 : Entails.eval a c8165 := derived8165 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8168 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8168 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c435, some c626, some c2001, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8168 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8168 : lratChecker f8168 p8168 = .success := by decide +kernel
theorem unsat8168 : Unsatisfiable (PosFin 65) f8168 := by
  apply lratCheckerSound f8168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8168
  · intro a ha; simp [p8168] at ha; subst a; trivial
  · exact checked8168
theorem derived8168 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8168 := by
  apply localUnsat_implies_entails f8168 [c435, c626, c2001] c8168 unsat8168 (by rfl) a
  have h0 : Entails.eval a c435 := h 434 (by decide)
  have h1 : Entails.eval a c626 := h 625 (by decide)
  have h2 : Entails.eval a c2001 := h 2000 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8169 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8169 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8160, some c8168, some c8159, some c8162, some c8166, some c8167, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8169 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8169 : lratChecker f8169 p8169 = .success := by decide +kernel
theorem unsat8169 : Unsatisfiable (PosFin 65) f8169 := by
  apply lratCheckerSound f8169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8169
  · intro a ha; simp [p8169] at ha; subst a; trivial
  · exact checked8169
theorem derived8169 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8169 := by
  apply localUnsat_implies_entails f8169 [c7849, c8160, c8168, c8159, c8162, c8166, c8167] c8169 unsat8169 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8160 := derived8160 a h
  have h2 : Entails.eval a c8168 := derived8168 a h
  have h3 : Entails.eval a c8159 := derived8159 a h
  have h4 : Entails.eval a c8162 := derived8162 a h
  have h5 : Entails.eval a c8166 := derived8166 a h
  have h6 : Entails.eval a c8167 := derived8167 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8170 : DefaultClause 65 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8170 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7849, some c8165, some c7766, some c1329, some c8067, some c1176, some c1280, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8170 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8170 : lratChecker f8170 p8170 = .success := by decide +kernel
theorem unsat8170 : Unsatisfiable (PosFin 65) f8170 := by
  apply lratCheckerSound f8170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8170
  · intro a ha; simp [p8170] at ha; subst a; trivial
  · exact checked8170
theorem derived8170 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8170 := by
  apply localUnsat_implies_entails f8170 [c7849, c8165, c7766, c1329, c8067, c1176, c1280] c8170 unsat8170 (by rfl) a
  have h0 : Entails.eval a c7849 := derived7849 a h
  have h1 : Entails.eval a c8165 := derived8165 a h
  have h2 : Entails.eval a c7766 := derived7766 a h
  have h3 : Entails.eval a c1329 := h 1328 (by decide)
  have h4 : Entails.eval a c8067 := derived8067 a h
  have h5 : Entails.eval a c1176 := h 1175 (by decide)
  have h6 : Entails.eval a c1280 := h 1279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8171 : DefaultClause 65 := directClause [(⟨31, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8171 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8159, some c7849, some c8160, some c8162, some c8168, some c8169, some c8170, some c1319, some c453, some c643, some c1976, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8171 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked8171 : lratChecker f8171 p8171 = .success := by decide +kernel
theorem unsat8171 : Unsatisfiable (PosFin 65) f8171 := by
  apply lratCheckerSound f8171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8171
  · intro a ha; simp [p8171] at ha; subst a; trivial
  · exact checked8171
theorem derived8171 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8171 := by
  apply localUnsat_implies_entails f8171 [c8159, c7849, c8160, c8162, c8168, c8169, c8170, c1319, c453, c643, c1976] c8171 unsat8171 (by rfl) a
  have h0 : Entails.eval a c8159 := derived8159 a h
  have h1 : Entails.eval a c7849 := derived7849 a h
  have h2 : Entails.eval a c8160 := derived8160 a h
  have h3 : Entails.eval a c8162 := derived8162 a h
  have h4 : Entails.eval a c8168 := derived8168 a h
  have h5 : Entails.eval a c8169 := derived8169 a h
  have h6 : Entails.eval a c8170 := derived8170 a h
  have h7 : Entails.eval a c1319 := h 1318 (by decide)
  have h8 : Entails.eval a c453 := h 452 (by decide)
  have h9 : Entails.eval a c643 := h 642 (by decide)
  have h10 : Entails.eval a c1976 := h 1975 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8172 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨28, by decide⟩, true), (⟨16, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8172 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c535, some c547, some c539, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8172 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8172 : lratChecker f8172 p8172 = .success := by decide +kernel
theorem unsat8172 : Unsatisfiable (PosFin 65) f8172 := by
  apply lratCheckerSound f8172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8172
  · intro a ha; simp [p8172] at ha; subst a; trivial
  · exact checked8172
theorem derived8172 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8172 := by
  apply localUnsat_implies_entails f8172 [c535, c547, c539] c8172 unsat8172 (by rfl) a
  have h0 : Entails.eval a c535 := h 534 (by decide)
  have h1 : Entails.eval a c547 := h 546 (by decide)
  have h2 : Entails.eval a c539 := h 538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8173 : DefaultClause 65 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨58, by decide⟩, true), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f8173 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8171, some c8159, some c7849, some c555, some c8172, some c8103, some c855, some c7961, some c530, some c7565, some c7941, some c7895, some c2671, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p8173 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked8173 : lratChecker f8173 p8173 = .success := by decide +kernel
theorem unsat8173 : Unsatisfiable (PosFin 65) f8173 := by
  apply lratCheckerSound f8173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8173
  · intro a ha; simp [p8173] at ha; subst a; trivial
  · exact checked8173
theorem derived8173 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8173 := by
  apply localUnsat_implies_entails f8173 [c8171, c8159, c7849, c555, c8172, c8103, c855, c7961, c530, c7565, c7941, c7895, c2671] c8173 unsat8173 (by rfl) a
  have h0 : Entails.eval a c8171 := derived8171 a h
  have h1 : Entails.eval a c8159 := derived8159 a h
  have h2 : Entails.eval a c7849 := derived7849 a h
  have h3 : Entails.eval a c555 := h 554 (by decide)
  have h4 : Entails.eval a c8172 := derived8172 a h
  have h5 : Entails.eval a c8103 := derived8103 a h
  have h6 : Entails.eval a c855 := h 854 (by decide)
  have h7 : Entails.eval a c7961 := derived7961 a h
  have h8 : Entails.eval a c530 := h 529 (by decide)
  have h9 : Entails.eval a c7565 := derived7565 a h
  have h10 : Entails.eval a c7941 := derived7941 a h
  have h11 : Entails.eval a c7895 := derived7895 a h
  have h12 : Entails.eval a c2671 := h 2670 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8174 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8174 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c1539, some c1256, some c1787, some c1809, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p8174 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8174 : lratChecker f8174 p8174 = .success := by decide +kernel
theorem unsat8174 : Unsatisfiable (PosFin 65) f8174 := by
  apply lratCheckerSound f8174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8174
  · intro a ha; simp [p8174] at ha; subst a; trivial
  · exact checked8174
theorem derived8174 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8174 := by
  apply localUnsat_implies_entails f8174 [c1539, c1256, c1787, c1809] c8174 unsat8174 (by rfl) a
  have h0 : Entails.eval a c1539 := h 1538 (by decide)
  have h1 : Entails.eval a c1256 := h 1255 (by decide)
  have h2 : Entails.eval a c1787 := h 1786 (by decide)
  have h3 : Entails.eval a c1809 := h 1808 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8175 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨29, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8175 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8174, some c1549, some c1267, some c1805, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p8175 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked8175 : lratChecker f8175 p8175 = .success := by decide +kernel
theorem unsat8175 : Unsatisfiable (PosFin 65) f8175 := by
  apply lratCheckerSound f8175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8175
  · intro a ha; simp [p8175] at ha; subst a; trivial
  · exact checked8175
theorem derived8175 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8175 := by
  apply localUnsat_implies_entails f8175 [c8174, c1549, c1267, c1805] c8175 unsat8175 (by rfl) a
  have h0 : Entails.eval a c8174 := derived8174 a h
  have h1 : Entails.eval a c1549 := h 1548 (by decide)
  have h2 : Entails.eval a c1267 := h 1266 (by decide)
  have h3 : Entails.eval a c1805 := h 1804 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c8176 : DefaultClause 65 := directClause [(⟨24, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8176 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c7946, some c1328, some c1174, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p8176 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8176 : lratChecker f8176 p8176 = .success := by decide +kernel
theorem unsat8176 : Unsatisfiable (PosFin 65) f8176 := by
  apply lratCheckerSound f8176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8176
  · intro a ha; simp [p8176] at ha; subst a; trivial
  · exact checked8176
theorem derived8176 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8176 := by
  apply localUnsat_implies_entails f8176 [c7946, c1328, c1174] c8176 unsat8176 (by rfl) a
  have h0 : Entails.eval a c7946 := derived7946 a h
  have h1 : Entails.eval a c1328 := h 1327 (by decide)
  have h2 : Entails.eval a c1174 := h 1173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8177 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨24, by decide⟩, false), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8177 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c623, some c431, some c1998, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8177 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8177 : lratChecker f8177 p8177 = .success := by decide +kernel
theorem unsat8177 : Unsatisfiable (PosFin 65) f8177 := by
  apply lratCheckerSound f8177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8177
  · intro a ha; simp [p8177] at ha; subst a; trivial
  · exact checked8177
theorem derived8177 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8177 := by
  apply localUnsat_implies_entails f8177 [c623, c431, c1998] c8177 unsat8177 (by rfl) a
  have h0 : Entails.eval a c623 := h 622 (by decide)
  have h1 : Entails.eval a c431 := h 430 (by decide)
  have h2 : Entails.eval a c1998 := h 1997 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8178 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨25, by decide⟩, false), (⟨19, by decide⟩, true), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8178 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c644, some c632, some c621, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8178 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked8178 : lratChecker f8178 p8178 = .success := by decide +kernel
theorem unsat8178 : Unsatisfiable (PosFin 65) f8178 := by
  apply lratCheckerSound f8178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8178
  · intro a ha; simp [p8178] at ha; subst a; trivial
  · exact checked8178
theorem derived8178 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8178 := by
  apply localUnsat_implies_entails f8178 [c644, c632, c621] c8178 unsat8178 (by rfl) a
  have h0 : Entails.eval a c644 := h 643 (by decide)
  have h1 : Entails.eval a c632 := h 631 (by decide)
  have h2 : Entails.eval a c621 := h 620 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c8179 : DefaultClause 65 := directClause [(⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8179 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8011, some c8176, some c1306, some c430, some c1039, some c1977, some c1041, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8179 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked8179 : lratChecker f8179 p8179 = .success := by decide +kernel
theorem unsat8179 : Unsatisfiable (PosFin 65) f8179 := by
  apply lratCheckerSound f8179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8179
  · intro a ha; simp [p8179] at ha; subst a; trivial
  · exact checked8179
theorem derived8179 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8179 := by
  apply localUnsat_implies_entails f8179 [c8011, c8176, c1306, c430, c1039, c1977, c1041] c8179 unsat8179 (by rfl) a
  have h0 : Entails.eval a c8011 := derived8011 a h
  have h1 : Entails.eval a c8176 := derived8176 a h
  have h2 : Entails.eval a c1306 := h 1305 (by decide)
  have h3 : Entails.eval a c430 := h 429 (by decide)
  have h4 : Entails.eval a c1039 := h 1038 (by decide)
  have h5 : Entails.eval a c1977 := h 1976 (by decide)
  have h6 : Entails.eval a c1041 := h 1040 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c8180 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f8180 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8175, some c8011, some c8176, some c8177, some c8179, some c441, some c2169, some c2122, some c2005, some c2620, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p8180 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked8180 : lratChecker f8180 p8180 = .success := by decide +kernel
theorem unsat8180 : Unsatisfiable (PosFin 65) f8180 := by
  apply lratCheckerSound f8180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p8180
  · intro a ha; simp [p8180] at ha; subst a; trivial
  · exact checked8180
theorem derived8180 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c8180 := by
  apply localUnsat_implies_entails f8180 [c8175, c8011, c8176, c8177, c8179, c441, c2169, c2122, c2005, c2620] c8180 unsat8180 (by rfl) a
  have h0 : Entails.eval a c8175 := derived8175 a h
  have h1 : Entails.eval a c8011 := derived8011 a h
  have h2 : Entails.eval a c8176 := derived8176 a h
  have h3 : Entails.eval a c8177 := derived8177 a h
  have h4 : Entails.eval a c8179 := derived8179 a h
  have h5 : Entails.eval a c441 := h 440 (by decide)
  have h6 : Entails.eval a c2169 := h 2168 (by decide)
  have h7 : Entails.eval a c2122 := h 2121 (by decide)
  have h8 : Entails.eval a c2005 := h 2004 (by decide)
  have h9 : Entails.eval a c2620 := h 2619 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived8180

end CochromaticTwenty.Certificates.FixedCore1
