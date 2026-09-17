import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps1600_1699

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c2114 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c980, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2114 : lratChecker f2114 p2114 = .success := by decide +kernel
theorem unsat2114 : Unsatisfiable (PosFin 57) f2114 := by
  apply lratCheckerSound f2114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2114
  · intro a ha; simp [p2114] at ha; subst a; trivial
  · exact checked2114
theorem derived2114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2114 := by
  apply localUnsat_implies_entails f2114 [c2068, c980] c2114 unsat2114 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c980 := derived980 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2115 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c31, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2115 : lratChecker f2115 p2115 = .success := by decide +kernel
theorem unsat2115 : Unsatisfiable (PosFin 57) f2115 := by
  apply lratCheckerSound f2115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2115
  · intro a ha; simp [p2115] at ha; subst a; trivial
  · exact checked2115
theorem derived2115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2115 := by
  apply localUnsat_implies_entails f2115 [c1829, c31] c2115 unsat2115 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2116 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c213, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2116 : lratChecker f2116 p2116 = .success := by decide +kernel
theorem unsat2116 : Unsatisfiable (PosFin 57) f2116 := by
  apply lratCheckerSound f2116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2116
  · intro a ha; simp [p2116] at ha; subst a; trivial
  · exact checked2116
theorem derived2116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2116 := by
  apply localUnsat_implies_entails f2116 [c2068, c213] c2116 unsat2116 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2117 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨36, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c225, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2117 : lratChecker f2117 p2117 = .success := by decide +kernel
theorem unsat2117 : Unsatisfiable (PosFin 57) f2117 := by
  apply lratCheckerSound f2117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2117
  · intro a ha; simp [p2117] at ha; subst a; trivial
  · exact checked2117
theorem derived2117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2117 := by
  apply localUnsat_implies_entails f2117 [c2068, c225] c2117 unsat2117 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2118 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c227, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p2118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2118 : lratChecker f2118 p2118 = .success := by decide +kernel
theorem unsat2118 : Unsatisfiable (PosFin 57) f2118 := by
  apply lratCheckerSound f2118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2118
  · intro a ha; simp [p2118] at ha; subst a; trivial
  · exact checked2118
theorem derived2118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2118 := by
  apply localUnsat_implies_entails f2118 [c2068, c227] c2118 unsat2118 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2119 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨40, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨17, by decide⟩, false), (⟨14, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c2006, some c972, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p2119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2119 : lratChecker f2119 p2119 = .success := by decide +kernel
theorem unsat2119 : Unsatisfiable (PosFin 57) f2119 := by
  apply lratCheckerSound f2119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2119
  · intro a ha; simp [p2119] at ha; subst a; trivial
  · exact checked2119
theorem derived2119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2119 := by
  apply localUnsat_implies_entails f2119 [c2068, c2006, c972] c2119 unsat2119 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c2006 := derived2006 a h
  have h2 : Entails.eval a c972 := derived972 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2120 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c235, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2120 : lratChecker f2120 p2120 = .success := by decide +kernel
theorem unsat2120 : Unsatisfiable (PosFin 57) f2120 := by
  apply lratCheckerSound f2120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2120
  · intro a ha; simp [p2120] at ha; subst a; trivial
  · exact checked2120
theorem derived2120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2120 := by
  apply localUnsat_implies_entails f2120 [c2006, c235] c2120 unsat2120 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2121 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c233, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2121 : lratChecker f2121 p2121 = .success := by decide +kernel
theorem unsat2121 : Unsatisfiable (PosFin 57) f2121 := by
  apply lratCheckerSound f2121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2121
  · intro a ha; simp [p2121] at ha; subst a; trivial
  · exact checked2121
theorem derived2121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2121 := by
  apply localUnsat_implies_entails f2121 [c2006, c233] c2121 unsat2121 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2122 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨51, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c249, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2122 : lratChecker f2122 p2122 = .success := by decide +kernel
theorem unsat2122 : Unsatisfiable (PosFin 57) f2122 := by
  apply lratCheckerSound f2122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2122
  · intro a ha; simp [p2122] at ha; subst a; trivial
  · exact checked2122
theorem derived2122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2122 := by
  apply localUnsat_implies_entails f2122 [c2006, c249] c2122 unsat2122 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2123 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c771, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2123 : lratChecker f2123 p2123 = .success := by decide +kernel
theorem unsat2123 : Unsatisfiable (PosFin 57) f2123 := by
  apply lratCheckerSound f2123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2123
  · intro a ha; simp [p2123] at ha; subst a; trivial
  · exact checked2123
theorem derived2123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2123 := by
  apply localUnsat_implies_entails f2123 [c2006, c771] c2123 unsat2123 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c771 := derived771 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2124 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c9, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2124 : lratChecker f2124 p2124 = .success := by decide +kernel
theorem unsat2124 : Unsatisfiable (PosFin 57) f2124 := by
  apply lratCheckerSound f2124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2124
  · intro a ha; simp [p2124] at ha; subst a; trivial
  · exact checked2124
theorem derived2124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2124 := by
  apply localUnsat_implies_entails f2124 [c1829, c9] c2124 unsat2124 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2125 : DefaultClause 57 := directClause ((⟨55, by decide⟩, false) :: (⟨49, by decide⟩, false) :: (⟨2, by decide⟩, true) :: (⟨56, by decide⟩, true) :: (⟨5, by decide⟩, false) :: (⟨4, by decide⟩, false) :: (⟨7, by decide⟩, true) :: (⟨6, by decide⟩, false) :: (⟨3, by decide⟩, true) :: (⟨11, by decide⟩, true) :: (⟨8, by decide⟩, false) :: (⟨12, by decide⟩, false) :: (⟨14, by decide⟩, true) :: (⟨15, by decide⟩, true) :: (⟨13, by decide⟩, false) :: (⟨10, by decide⟩, false) :: (⟨17, by decide⟩, true) :: (⟨16, by decide⟩, true) :: (⟨19, by decide⟩, false) :: (⟨9, by decide⟩, false) :: (⟨20, by decide⟩, true) :: (⟨21, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨22, by decide⟩, false) :: (⟨27, by decide⟩, false) :: (⟨25, by decide⟩, true) :: (⟨29, by decide⟩, true) :: (⟨23, by decide⟩, false) :: (⟨31, by decide⟩, false) :: (⟨32, by decide⟩, false) :: (⟨33, by decide⟩, false) :: (⟨28, by decide⟩, false) :: (⟨30, by decide⟩, true) :: (⟨36, by decide⟩, true) :: (⟨54, by decide⟩, false) :: (⟨38, by decide⟩, true) :: (⟨40, by decide⟩, false) :: (⟨39, by decide⟩, true) :: (⟨37, by decide⟩, true) :: (⟨41, by decide⟩, false) :: (⟨43, by decide⟩, false) :: (⟨42, by decide⟩, true) :: (⟨46, by decide⟩, false) :: (⟨47, by decide⟩, true) :: (⟨48, by decide⟩, true) :: (⟨44, by decide⟩, true) :: (⟨35, by decide⟩, false) :: (⟨34, by decide⟩, false) :: (⟨52, by decide⟩, false) :: (⟨51, by decide⟩, true) :: (⟨45, by decide⟩, false) :: (⟨50, by decide⟩, true) :: (⟨53, by decide⟩, true) :: []) (by decide +kernel) (by decide +kernel)
def f2125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c2068, some c2006, some c411, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p2125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2125 : lratChecker f2125 p2125 = .success := by decide +kernel
theorem unsat2125 : Unsatisfiable (PosFin 57) f2125 := by
  apply lratCheckerSound f2125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2125
  · intro a ha; simp [p2125] at ha; subst a; trivial
  · exact checked2125
theorem derived2125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2125 := by
  apply localUnsat_implies_entails f2125 [c1829, c2068, c2006, c411] c2125 unsat2125 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c2006 := derived2006 a h
  have h3 : Entails.eval a c411 := h 410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2126 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p2126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2126 : lratChecker f2126 p2126 = .success := by decide +kernel
theorem unsat2126 : Unsatisfiable (PosFin 57) f2126 := by
  apply lratCheckerSound f2126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2126
  · intro a ha; simp [p2126] at ha; subst a; trivial
  · exact checked2126
theorem derived2126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2126 := by
  apply localUnsat_implies_entails f2126 [c1829, c1] c2126 unsat2126 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2127 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c95, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p2127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2127 : lratChecker f2127 p2127 = .success := by decide +kernel
theorem unsat2127 : Unsatisfiable (PosFin 57) f2127 := by
  apply lratCheckerSound f2127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2127
  · intro a ha; simp [p2127] at ha; subst a; trivial
  · exact checked2127
theorem derived2127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2127 := by
  apply localUnsat_implies_entails f2127 [c1829, c95] c2127 unsat2127 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2128 : DefaultClause 57 := directClause ((⟨55, by decide⟩, false) :: (⟨56, by decide⟩, false) :: (⟨54, by decide⟩, true) :: (⟨4, by decide⟩, false) :: (⟨5, by decide⟩, true) :: (⟨6, by decide⟩, true) :: (⟨3, by decide⟩, false) :: (⟨7, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨10, by decide⟩, false) :: (⟨2, by decide⟩, true) :: (⟨9, by decide⟩, true) :: (⟨11, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨15, by decide⟩, false) :: (⟨16, by decide⟩, true) :: (⟨12, by decide⟩, true) :: (⟨19, by decide⟩, true) :: (⟨20, by decide⟩, false) :: (⟨21, by decide⟩, false) :: (⟨22, by decide⟩, true) :: (⟨23, by decide⟩, true) :: (⟨25, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨27, by decide⟩, true) :: (⟨28, by decide⟩, false) :: (⟨17, by decide⟩, false) :: (⟨14, by decide⟩, false) :: (⟨31, by decide⟩, true) :: (⟨30, by decide⟩, false) :: (⟨32, by decide⟩, false) :: (⟨35, by decide⟩, false) :: (⟨36, by decide⟩, true) :: (⟨37, by decide⟩, false) :: (⟨38, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨40, by decide⟩, true) :: (⟨33, by decide⟩, false) :: (⟨41, by decide⟩, false) :: (⟨43, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, true) :: (⟨42, by decide⟩, false) :: (⟨47, by decide⟩, true) :: (⟨48, by decide⟩, false) :: (⟨46, by decide⟩, true) :: (⟨39, by decide⟩, true) :: (⟨51, by decide⟩, true) :: (⟨52, by decide⟩, true) :: (⟨53, by decide⟩, false) :: (⟨49, by decide⟩, true) :: (⟨50, by decide⟩, false) :: []) (by decide +kernel) (by decide +kernel)
def f2128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2068, some c1829, some c677, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p2128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2128 : lratChecker f2128 p2128 = .success := by decide +kernel
theorem unsat2128 : Unsatisfiable (PosFin 57) f2128 := by
  apply lratCheckerSound f2128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2128
  · intro a ha; simp [p2128] at ha; subst a; trivial
  · exact checked2128
theorem derived2128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2128 := by
  apply localUnsat_implies_entails f2128 [c2006, c2068, c1829, c677] c2128 unsat2128 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c1829 := derived1829 a h
  have h3 : Entails.eval a c677 := derived677 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2129 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c10, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2129 : lratChecker f2129 p2129 = .success := by decide +kernel
theorem unsat2129 : Unsatisfiable (PosFin 57) f2129 := by
  apply lratCheckerSound f2129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2129
  · intro a ha; simp [p2129] at ha; subst a; trivial
  · exact checked2129
theorem derived2129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2129 := by
  apply localUnsat_implies_entails f2129 [c1829, c10] c2129 unsat2129 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2130 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c215, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p2130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2130 : lratChecker f2130 p2130 = .success := by decide +kernel
theorem unsat2130 : Unsatisfiable (PosFin 57) f2130 := by
  apply lratCheckerSound f2130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2130
  · intro a ha; simp [p2130] at ha; subst a; trivial
  · exact checked2130
theorem derived2130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2130 := by
  apply localUnsat_implies_entails f2130 [c2068, c215] c2130 unsat2130 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2131 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c211, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2131 : lratChecker f2131 p2131 = .success := by decide +kernel
theorem unsat2131 : Unsatisfiable (PosFin 57) f2131 := by
  apply lratCheckerSound f2131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2131
  · intro a ha; simp [p2131] at ha; subst a; trivial
  · exact checked2131
theorem derived2131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2131 := by
  apply localUnsat_implies_entails f2131 [c2068, c211] c2131 unsat2131 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2132 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c469, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p2132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2132 : lratChecker f2132 p2132 = .success := by decide +kernel
theorem unsat2132 : Unsatisfiable (PosFin 57) f2132 := by
  apply lratCheckerSound f2132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2132
  · intro a ha; simp [p2132] at ha; subst a; trivial
  · exact checked2132
theorem derived2132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2132 := by
  apply localUnsat_implies_entails f2132 [c2068, c469] c2132 unsat2132 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c469 := derived469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2133 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c473, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2133 : lratChecker f2133 p2133 = .success := by decide +kernel
theorem unsat2133 : Unsatisfiable (PosFin 57) f2133 := by
  apply lratCheckerSound f2133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2133
  · intro a ha; simp [p2133] at ha; subst a; trivial
  · exact checked2133
theorem derived2133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2133 := by
  apply localUnsat_implies_entails f2133 [c1829, c473] c2133 unsat2133 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c473 := derived473 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2134 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1094, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p2134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2134 : lratChecker f2134 p2134 = .success := by decide +kernel
theorem unsat2134 : Unsatisfiable (PosFin 57) f2134 := by
  apply lratCheckerSound f2134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2134
  · intro a ha; simp [p2134] at ha; subst a; trivial
  · exact checked2134
theorem derived2134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2134 := by
  apply localUnsat_implies_entails f2134 [c2068, c1094] c2134 unsat2134 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1094 := derived1094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2135 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c251, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2135 : lratChecker f2135 p2135 = .success := by decide +kernel
theorem unsat2135 : Unsatisfiable (PosFin 57) f2135 := by
  apply lratCheckerSound f2135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2135
  · intro a ha; simp [p2135] at ha; subst a; trivial
  · exact checked2135
theorem derived2135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2135 := by
  apply localUnsat_implies_entails f2135 [c2006, c251] c2135 unsat2135 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2136 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c28, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p2136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2136 : lratChecker f2136 p2136 = .success := by decide +kernel
theorem unsat2136 : Unsatisfiable (PosFin 57) f2136 := by
  apply lratCheckerSound f2136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2136
  · intro a ha; simp [p2136] at ha; subst a; trivial
  · exact checked2136
theorem derived2136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2136 := by
  apply localUnsat_implies_entails f2136 [c2068, c28] c2136 unsat2136 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2137 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c223, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p2137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2137 : lratChecker f2137 p2137 = .success := by decide +kernel
theorem unsat2137 : Unsatisfiable (PosFin 57) f2137 := by
  apply lratCheckerSound f2137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2137
  · intro a ha; simp [p2137] at ha; subst a; trivial
  · exact checked2137
theorem derived2137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2137 := by
  apply localUnsat_implies_entails f2137 [c2068, c223] c2137 unsat2137 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2138 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨6, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1211, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2138 : lratChecker f2138 p2138 = .success := by decide +kernel
theorem unsat2138 : Unsatisfiable (PosFin 57) f2138 := by
  apply lratCheckerSound f2138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2138
  · intro a ha; simp [p2138] at ha; subst a; trivial
  · exact checked2138
theorem derived2138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2138 := by
  apply localUnsat_implies_entails f2138 [c2068, c1211] c2138 unsat2138 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1211 := derived1211 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2139 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1215, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p2139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2139 : lratChecker f2139 p2139 = .success := by decide +kernel
theorem unsat2139 : Unsatisfiable (PosFin 57) f2139 := by
  apply lratCheckerSound f2139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2139
  · intro a ha; simp [p2139] at ha; subst a; trivial
  · exact checked2139
theorem derived2139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2139 := by
  apply localUnsat_implies_entails f2139 [c2068, c1215] c2139 unsat2139 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1215 := derived1215 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2140 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨21, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨39, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1232, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p2140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2140 : lratChecker f2140 p2140 = .success := by decide +kernel
theorem unsat2140 : Unsatisfiable (PosFin 57) f2140 := by
  apply lratCheckerSound f2140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2140
  · intro a ha; simp [p2140] at ha; subst a; trivial
  · exact checked2140
theorem derived2140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2140 := by
  apply localUnsat_implies_entails f2140 [c1829, c1232] c2140 unsat2140 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1232 := derived1232 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2141 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨36, by decide⟩, true), (⟨14, by decide⟩, false), (⟨38, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1829, some c1257, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true))]
def p2141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2141 : lratChecker f2141 p2141 = .success := by decide +kernel
theorem unsat2141 : Unsatisfiable (PosFin 57) f2141 := by
  apply lratCheckerSound f2141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2141
  · intro a ha; simp [p2141] at ha; subst a; trivial
  · exact checked2141
theorem derived2141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2141 := by
  apply localUnsat_implies_entails f2141 [c1829, c1257] c2141 unsat2141 (by rfl) a
  have h0 : Entails.eval a c1829 := derived1829 a h
  have h1 : Entails.eval a c1257 := derived1257 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2142 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1292, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2142 : lratChecker f2142 p2142 = .success := by decide +kernel
theorem unsat2142 : Unsatisfiable (PosFin 57) f2142 := by
  apply lratCheckerSound f2142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2142
  · intro a ha; simp [p2142] at ha; subst a; trivial
  · exact checked2142
theorem derived2142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2142 := by
  apply localUnsat_implies_entails f2142 [c2006, c1292] c2142 unsat2142 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1292 := derived1292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2143 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1299, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2143 : lratChecker f2143 p2143 = .success := by decide +kernel
theorem unsat2143 : Unsatisfiable (PosFin 57) f2143 := by
  apply lratCheckerSound f2143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2143
  · intro a ha; simp [p2143] at ha; subst a; trivial
  · exact checked2143
theorem derived2143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2143 := by
  apply localUnsat_implies_entails f2143 [c2006, c1299] c2143 unsat2143 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1299 := derived1299 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2144 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨11, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c2068, some c1348, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p2144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2144 : lratChecker f2144 p2144 = .success := by decide +kernel
theorem unsat2144 : Unsatisfiable (PosFin 57) f2144 := by
  apply lratCheckerSound f2144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2144
  · intro a ha; simp [p2144] at ha; subst a; trivial
  · exact checked2144
theorem derived2144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2144 := by
  apply localUnsat_implies_entails f2144 [c2006, c2068, c1348] c2144 unsat2144 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c2068 := derived2068 a h
  have h2 : Entails.eval a c1348 := derived1348 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2145 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1484, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p2145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2145 : lratChecker f2145 p2145 = .success := by decide +kernel
theorem unsat2145 : Unsatisfiable (PosFin 57) f2145 := by
  apply lratCheckerSound f2145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2145
  · intro a ha; simp [p2145] at ha; subst a; trivial
  · exact checked2145
theorem derived2145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2145 := by
  apply localUnsat_implies_entails f2145 [c2006, c1484] c2145 unsat2145 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1484 := derived1484 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2146 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1498, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p2146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2146 : lratChecker f2146 p2146 = .success := by decide +kernel
theorem unsat2146 : Unsatisfiable (PosFin 57) f2146 := by
  apply lratCheckerSound f2146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2146
  · intro a ha; simp [p2146] at ha; subst a; trivial
  · exact checked2146
theorem derived2146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2146 := by
  apply localUnsat_implies_entails f2146 [c2006, c1498] c2146 unsat2146 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1498 := derived1498 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2147 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨20, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1695, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p2147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2147 : lratChecker f2147 p2147 = .success := by decide +kernel
theorem unsat2147 : Unsatisfiable (PosFin 57) f2147 := by
  apply lratCheckerSound f2147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2147
  · intro a ha; simp [p2147] at ha; subst a; trivial
  · exact checked2147
theorem derived2147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2147 := by
  apply localUnsat_implies_entails f2147 [c2068, c1695] c2147 unsat2147 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1695 := derived1695 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2148 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1708, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p2148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2148 : lratChecker f2148 p2148 = .success := by decide +kernel
theorem unsat2148 : Unsatisfiable (PosFin 57) f2148 := by
  apply lratCheckerSound f2148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2148
  · intro a ha; simp [p2148] at ha; subst a; trivial
  · exact checked2148
theorem derived2148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2148 := by
  apply localUnsat_implies_entails f2148 [c2006, c1708] c2148 unsat2148 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1708 := derived1708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2149 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨2, by decide⟩, true), (⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1757, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p2149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2149 : lratChecker f2149 p2149 = .success := by decide +kernel
theorem unsat2149 : Unsatisfiable (PosFin 57) f2149 := by
  apply lratCheckerSound f2149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2149
  · intro a ha; simp [p2149] at ha; subst a; trivial
  · exact checked2149
theorem derived2149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2149 := by
  apply localUnsat_implies_entails f2149 [c2068, c1757] c2149 unsat2149 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1757 := derived1757 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2150 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1768, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2150 : lratChecker f2150 p2150 = .success := by decide +kernel
theorem unsat2150 : Unsatisfiable (PosFin 57) f2150 := by
  apply lratCheckerSound f2150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2150
  · intro a ha; simp [p2150] at ha; subst a; trivial
  · exact checked2150
theorem derived2150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2150 := by
  apply localUnsat_implies_entails f2150 [c2068, c1768] c2150 unsat2150 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1768 := derived1768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2151 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1769, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2151 : lratChecker f2151 p2151 = .success := by decide +kernel
theorem unsat2151 : Unsatisfiable (PosFin 57) f2151 := by
  apply lratCheckerSound f2151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2151
  · intro a ha; simp [p2151] at ha; subst a; trivial
  · exact checked2151
theorem derived2151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2151 := by
  apply localUnsat_implies_entails f2151 [c2068, c1769] c2151 unsat2151 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1769 := derived1769 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2152 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2006, some c1777, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p2152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2152 : lratChecker f2152 p2152 = .success := by decide +kernel
theorem unsat2152 : Unsatisfiable (PosFin 57) f2152 := by
  apply lratCheckerSound f2152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2152
  · intro a ha; simp [p2152] at ha; subst a; trivial
  · exact checked2152
theorem derived2152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2152 := by
  apply localUnsat_implies_entails f2152 [c2006, c1777] c2152 unsat2152 (by rfl) a
  have h0 : Entails.eval a c2006 := derived2006 a h
  have h1 : Entails.eval a c1777 := derived1777 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2153 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1944, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p2153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2153 : lratChecker f2153 p2153 = .success := by decide +kernel
theorem unsat2153 : Unsatisfiable (PosFin 57) f2153 := by
  apply lratCheckerSound f2153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2153
  · intro a ha; simp [p2153] at ha; subst a; trivial
  · exact checked2153
theorem derived2153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2153 := by
  apply localUnsat_implies_entails f2153 [c2068, c1944] c2153 unsat2153 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1944 := derived1944 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2154 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false), (⟨23, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false), (⟨2, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2068, some c1985, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2154 : lratChecker f2154 p2154 = .success := by decide +kernel
theorem unsat2154 : Unsatisfiable (PosFin 57) f2154 := by
  apply lratCheckerSound f2154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2154
  · intro a ha; simp [p2154] at ha; subst a; trivial
  · exact checked2154
theorem derived2154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2154 := by
  apply localUnsat_implies_entails f2154 [c2068, c1985] c2154 unsat2154 (by rfl) a
  have h0 : Entails.eval a c2068 := derived2068 a h
  have h1 : Entails.eval a c1985 := derived1985 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2155 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨6, by decide⟩, true), (⟨26, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1500, some c141, some c1489, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p2155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked2155 : lratChecker f2155 p2155 = .success := by decide +kernel
theorem unsat2155 : Unsatisfiable (PosFin 57) f2155 := by
  apply lratCheckerSound f2155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2155
  · intro a ha; simp [p2155] at ha; subst a; trivial
  · exact checked2155
theorem derived2155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2155 := by
  apply localUnsat_implies_entails f2155 [c1500, c141, c1489] c2155 unsat2155 (by rfl) a
  have h0 : Entails.eval a c1500 := derived1500 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c1489 := derived1489 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c2156 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c819, some c2007, some c2101, some c3, some c48, some c145, some c314, some c56, some c2155, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2156 : lratChecker f2156 p2156 = .success := by decide +kernel
theorem unsat2156 : Unsatisfiable (PosFin 57) f2156 := by
  apply lratCheckerSound f2156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2156
  · intro a ha; simp [p2156] at ha; subst a; trivial
  · exact checked2156
theorem derived2156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2156 := by
  apply localUnsat_implies_entails f2156 [c819, c2007, c2101, c3, c48, c145, c314, c56, c2155] c2156 unsat2156 (by rfl) a
  have h0 : Entails.eval a c819 := derived819 a h
  have h1 : Entails.eval a c2007 := derived2007 a h
  have h2 : Entails.eval a c2101 := derived2101 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c2155 := derived2155 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2157 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2080, some c20, some c1489, some c2113, some c2092, some c76, some c153, some c348, some c2118, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2157 : lratChecker f2157 p2157 = .success := by decide +kernel
theorem unsat2157 : Unsatisfiable (PosFin 57) f2157 := by
  apply lratCheckerSound f2157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2157
  · intro a ha; simp [p2157] at ha; subst a; trivial
  · exact checked2157
theorem derived2157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2157 := by
  apply localUnsat_implies_entails f2157 [c2080, c20, c1489, c2113, c2092, c76, c153, c348, c2118] c2157 unsat2157 (by rfl) a
  have h0 : Entails.eval a c2080 := derived2080 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c1489 := derived1489 a h
  have h3 : Entails.eval a c2113 := derived2113 a h
  have h4 : Entails.eval a c2092 := derived2092 a h
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c348 := h 347 (by decide)
  have h8 : Entails.eval a c2118 := derived2118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2158 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨21, by decide⟩, true), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2115, some c198, some c2073, some c2077, some c207, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2158 : lratChecker f2158 p2158 = .success := by decide +kernel
theorem unsat2158 : Unsatisfiable (PosFin 57) f2158 := by
  apply lratCheckerSound f2158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2158
  · intro a ha; simp [p2158] at ha; subst a; trivial
  · exact checked2158
theorem derived2158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2158 := by
  apply localUnsat_implies_entails f2158 [c2115, c198, c2073, c2077, c207] c2158 unsat2158 (by rfl) a
  have h0 : Entails.eval a c2115 := derived2115 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c2073 := derived2073 a h
  have h3 : Entails.eval a c2077 := derived2077 a h
  have h4 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2159 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨19, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c2085, some c2157, some c2158, some c2093, some c2146, some c2092, some c2153, some c203, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2159 : lratChecker f2159 p2159 = .success := by decide +kernel
theorem unsat2159 : Unsatisfiable (PosFin 57) f2159 := by
  apply lratCheckerSound f2159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2159
  · intro a ha; simp [p2159] at ha; subst a; trivial
  · exact checked2159
theorem derived2159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2159 := by
  apply localUnsat_implies_entails f2159 [c268, c2085, c2157, c2158, c2093, c2146, c2092, c2153, c203] c2159 unsat2159 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2157 := derived2157 a h
  have h3 : Entails.eval a c2158 := derived2158 a h
  have h4 : Entails.eval a c2093 := derived2093 a h
  have h5 : Entails.eval a c2146 := derived2146 a h
  have h6 : Entails.eval a c2092 := derived2092 a h
  have h7 : Entails.eval a c2153 := derived2153 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2160 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c819, some c48, some c56, some c145, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2160 : lratChecker f2160 p2160 = .success := by decide +kernel
theorem unsat2160 : Unsatisfiable (PosFin 57) f2160 := by
  apply lratCheckerSound f2160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2160
  · intro a ha; simp [p2160] at ha; subst a; trivial
  · exact checked2160
theorem derived2160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2160 := by
  apply localUnsat_implies_entails f2160 [c819, c48, c56, c145] c2160 unsat2160 (by rfl) a
  have h0 : Entails.eval a c819 := derived819 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2161 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2007, some c2078, some c819, some c2069, some c2156, some c2159, some c1489, some c198, some c2160, some c2136, some c1019, some c156, some c2081, some c246, some c98, some c62, some c2122, some c283, some c351, some c338, some c152, some c284, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked2161 : lratChecker f2161 p2161 = .success := by decide +kernel
theorem unsat2161 : Unsatisfiable (PosFin 57) f2161 := by
  apply lratCheckerSound f2161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2161
  · intro a ha; simp [p2161] at ha; subst a; trivial
  · exact checked2161
theorem derived2161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2161 := by
  apply localUnsat_implies_entails f2161 [c2007, c2078, c819, c2069, c2156, c2159, c1489, c198, c2160, c2136, c1019, c156, c2081, c246, c98, c62, c2122, c283, c351, c338, c152, c284] c2161 unsat2161 (by rfl) a
  have h0 : Entails.eval a c2007 := derived2007 a h
  have h1 : Entails.eval a c2078 := derived2078 a h
  have h2 : Entails.eval a c819 := derived819 a h
  have h3 : Entails.eval a c2069 := derived2069 a h
  have h4 : Entails.eval a c2156 := derived2156 a h
  have h5 : Entails.eval a c2159 := derived2159 a h
  have h6 : Entails.eval a c1489 := derived1489 a h
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c2160 := derived2160 a h
  have h9 : Entails.eval a c2136 := derived2136 a h
  have h10 : Entails.eval a c1019 := derived1019 a h
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c2081 := derived2081 a h
  have h13 : Entails.eval a c246 := h 245 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c2122 := derived2122 a h
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c351 := h 350 (by decide)
  have h19 : Entails.eval a c338 := h 337 (by decide)
  have h20 : Entails.eval a c152 := h 151 (by decide)
  have h21 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2162 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨43, by decide⟩, true), (⟨21, by decide⟩, true), (⟨32, by decide⟩, false), (⟨10, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2093, some c2146, some c2092, some c48, some c203, some c134, some c175, some c84, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p2162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2162 : lratChecker f2162 p2162 = .success := by decide +kernel
theorem unsat2162 : Unsatisfiable (PosFin 57) f2162 := by
  apply lratCheckerSound f2162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2162
  · intro a ha; simp [p2162] at ha; subst a; trivial
  · exact checked2162
theorem derived2162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2162 := by
  apply localUnsat_implies_entails f2162 [c2093, c2146, c2092, c48, c203, c134, c175, c84] c2162 unsat2162 (by rfl) a
  have h0 : Entails.eval a c2093 := derived2093 a h
  have h1 : Entails.eval a c2146 := derived2146 a h
  have h2 : Entails.eval a c2092 := derived2092 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c175 := h 174 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2163 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨14, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c24, some c1229, some c161, some c70, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2163 : lratChecker f2163 p2163 = .success := by decide +kernel
theorem unsat2163 : Unsatisfiable (PosFin 57) f2163 := by
  apply lratCheckerSound f2163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2163
  · intro a ha; simp [p2163] at ha; subst a; trivial
  · exact checked2163
theorem derived2163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2163 := by
  apply localUnsat_implies_entails f2163 [c4, c24, c1229, c161, c70] c2163 unsat2163 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c1229 := derived1229 a h
  have h3 : Entails.eval a c161 := h 160 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2164 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨16, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2136, some c1019, some c63, some c104, some c348, some c246, some c2081, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p2164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2164 : lratChecker f2164 p2164 = .success := by decide +kernel
theorem unsat2164 : Unsatisfiable (PosFin 57) f2164 := by
  apply lratCheckerSound f2164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2164
  · intro a ha; simp [p2164] at ha; subst a; trivial
  · exact checked2164
theorem derived2164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2164 := by
  apply localUnsat_implies_entails f2164 [c2136, c1019, c63, c104, c348, c246, c2081] c2164 unsat2164 (by rfl) a
  have h0 : Entails.eval a c2136 := derived2136 a h
  have h1 : Entails.eval a c1019 := derived1019 a h
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c2081 := derived2081 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2165 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c819, some c145, some c141, some c314, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2165 : lratChecker f2165 p2165 = .success := by decide +kernel
theorem unsat2165 : Unsatisfiable (PosFin 57) f2165 := by
  apply lratCheckerSound f2165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2165
  · intro a ha; simp [p2165] at ha; subst a; trivial
  · exact checked2165
theorem derived2165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2165 := by
  apply localUnsat_implies_entails f2165 [c819, c145, c141, c314] c2165 unsat2165 (by rfl) a
  have h0 : Entails.eval a c819 := derived819 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2166 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2007, some c2085, some c2069, some c2078, some c819, some c2156, some c268, some c2123, some c2162, some c2161, some c2126, some c2129, some c2165, some c48, some c317, some c2136, some c2143, some c2164, some c46, some c116, some c203, some c835, some c139, some c152, some c727, some c167, some c272, some c62, some c2081, some c246, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked2166 : lratChecker f2166 p2166 = .success := by decide +kernel
theorem unsat2166 : Unsatisfiable (PosFin 57) f2166 := by
  apply lratCheckerSound f2166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2166
  · intro a ha; simp [p2166] at ha; subst a; trivial
  · exact checked2166
theorem derived2166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2166 := by
  apply localUnsat_implies_entails f2166 [c2007, c2085, c2069, c2078, c819, c2156, c268, c2123, c2162, c2161, c2126, c2129, c2165, c48, c317, c2136, c2143, c2164, c46, c116, c203, c835, c139, c152, c727, c167, c272, c62, c2081, c246] c2166 unsat2166 (by rfl) a
  have h0 : Entails.eval a c2007 := derived2007 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2069 := derived2069 a h
  have h3 : Entails.eval a c2078 := derived2078 a h
  have h4 : Entails.eval a c819 := derived819 a h
  have h5 : Entails.eval a c2156 := derived2156 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c2123 := derived2123 a h
  have h8 : Entails.eval a c2162 := derived2162 a h
  have h9 : Entails.eval a c2161 := derived2161 a h
  have h10 : Entails.eval a c2126 := derived2126 a h
  have h11 : Entails.eval a c2129 := derived2129 a h
  have h12 : Entails.eval a c2165 := derived2165 a h
  have h13 : Entails.eval a c48 := h 47 (by decide)
  have h14 : Entails.eval a c317 := h 316 (by decide)
  have h15 : Entails.eval a c2136 := derived2136 a h
  have h16 : Entails.eval a c2143 := derived2143 a h
  have h17 : Entails.eval a c2164 := derived2164 a h
  have h18 : Entails.eval a c46 := h 45 (by decide)
  have h19 : Entails.eval a c116 := h 115 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c835 := derived835 a h
  have h22 : Entails.eval a c139 := h 138 (by decide)
  have h23 : Entails.eval a c152 := h 151 (by decide)
  have h24 : Entails.eval a c727 := derived727 a h
  have h25 : Entails.eval a c167 := h 166 (by decide)
  have h26 : Entails.eval a c272 := h 271 (by decide)
  have h27 : Entails.eval a c62 := h 61 (by decide)
  have h28 : Entails.eval a c2081 := derived2081 a h
  have h29 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2167 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2166, some c2007, some c1147, some c26, some c2113, some c261, some c38, some c108, some c112, some c604, some c72, some c2083, some c346, some c348, some c2118, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2167 : lratChecker f2167 p2167 = .success := by decide +kernel
theorem unsat2167 : Unsatisfiable (PosFin 57) f2167 := by
  apply lratCheckerSound f2167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2167
  · intro a ha; simp [p2167] at ha; subst a; trivial
  · exact checked2167
theorem derived2167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2167 := by
  apply localUnsat_implies_entails f2167 [c2166, c2007, c1147, c26, c2113, c261, c38, c108, c112, c604, c72, c2083, c346, c348, c2118] c2167 unsat2167 (by rfl) a
  have h0 : Entails.eval a c2166 := derived2166 a h
  have h1 : Entails.eval a c2007 := derived2007 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c2113 := derived2113 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c604 := derived604 a h
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c2083 := derived2083 a h
  have h12 : Entails.eval a c346 := h 345 (by decide)
  have h13 : Entails.eval a c348 := h 347 (by decide)
  have h14 : Entails.eval a c2118 := derived2118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2168 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2166, some c1147, some c2007, some c2167, some c34, some c2086, some c2094, some c819, some c26, some c198, some c154, some c2093, some c2160, some c1262, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2168 : lratChecker f2168 p2168 = .success := by decide +kernel
theorem unsat2168 : Unsatisfiable (PosFin 57) f2168 := by
  apply lratCheckerSound f2168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2168
  · intro a ha; simp [p2168] at ha; subst a; trivial
  · exact checked2168
theorem derived2168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2168 := by
  apply localUnsat_implies_entails f2168 [c2166, c1147, c2007, c2167, c34, c2086, c2094, c819, c26, c198, c154, c2093, c2160, c1262] c2168 unsat2168 (by rfl) a
  have h0 : Entails.eval a c2166 := derived2166 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c2007 := derived2007 a h
  have h3 : Entails.eval a c2167 := derived2167 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c2086 := derived2086 a h
  have h6 : Entails.eval a c2094 := derived2094 a h
  have h7 : Entails.eval a c819 := derived819 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c2093 := derived2093 a h
  have h12 : Entails.eval a c2160 := derived2160 a h
  have h13 : Entails.eval a c1262 := derived1262 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2169 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2007, some c2166, some c1147, some c26, some c2113, some c261, some c2167, some c34, some c2086, some c2139, some c2094, some c1229, some c2168, some c2129, some c2165, some c203, some c46, some c116, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2169 : lratChecker f2169 p2169 = .success := by decide +kernel
theorem unsat2169 : Unsatisfiable (PosFin 57) f2169 := by
  apply lratCheckerSound f2169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2169
  · intro a ha; simp [p2169] at ha; subst a; trivial
  · exact checked2169
theorem derived2169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2169 := by
  apply localUnsat_implies_entails f2169 [c2007, c2166, c1147, c26, c2113, c261, c2167, c34, c2086, c2139, c2094, c1229, c2168, c2129, c2165, c203, c46, c116] c2169 unsat2169 (by rfl) a
  have h0 : Entails.eval a c2007 := derived2007 a h
  have h1 : Entails.eval a c2166 := derived2166 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c2113 := derived2113 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c2167 := derived2167 a h
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c2086 := derived2086 a h
  have h9 : Entails.eval a c2139 := derived2139 a h
  have h10 : Entails.eval a c2094 := derived2094 a h
  have h11 : Entails.eval a c1229 := derived1229 a h
  have h12 : Entails.eval a c2168 := derived2168 a h
  have h13 : Entails.eval a c2129 := derived2129 a h
  have h14 : Entails.eval a c2165 := derived2165 a h
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c46 := h 45 (by decide)
  have h17 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2170 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2169, some c2085, some c128, some c119, some c7, some c2007, some c108, some c112, some c51, some c2143, some c24, some c2160, some c56, some c2094, some c200, some c2116, some c18, some c146, some c164, some c281, some c74, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked2170 : lratChecker f2170 p2170 = .success := by decide +kernel
theorem unsat2170 : Unsatisfiable (PosFin 57) f2170 := by
  apply lratCheckerSound f2170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2170
  · intro a ha; simp [p2170] at ha; subst a; trivial
  · exact checked2170
theorem derived2170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2170 := by
  apply localUnsat_implies_entails f2170 [c2169, c2085, c128, c119, c7, c2007, c108, c112, c51, c2143, c24, c2160, c56, c2094, c200, c2116, c18, c146, c164, c281, c74] c2170 unsat2170 (by rfl) a
  have h0 : Entails.eval a c2169 := derived2169 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c2007 := derived2007 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c2143 := derived2143 a h
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c2160 := derived2160 a h
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c2094 := derived2094 a h
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c2116 := derived2116 a h
  have h16 : Entails.eval a c18 := h 17 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  have h20 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2171 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2169, some c119, some c7, some c2007, some c2085, some c128, some c2170, some c1931, some c819, some c2160, some c2136, some c1955, some c284, some c224, some c161, some c2082, some c70, some c347, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2171 : lratChecker f2171 p2171 = .success := by decide +kernel
theorem unsat2171 : Unsatisfiable (PosFin 57) f2171 := by
  apply lratCheckerSound f2171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2171
  · intro a ha; simp [p2171] at ha; subst a; trivial
  · exact checked2171
theorem derived2171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2171 := by
  apply localUnsat_implies_entails f2171 [c2169, c119, c7, c2007, c2085, c128, c2170, c1931, c819, c2160, c2136, c1955, c284, c224, c161, c2082, c70, c347] c2171 unsat2171 (by rfl) a
  have h0 : Entails.eval a c2169 := derived2169 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c2007 := derived2007 a h
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c2170 := derived2170 a h
  have h7 : Entails.eval a c1931 := derived1931 a h
  have h8 : Entails.eval a c819 := derived819 a h
  have h9 : Entails.eval a c2160 := derived2160 a h
  have h10 : Entails.eval a c2136 := derived2136 a h
  have h11 : Entails.eval a c1955 := derived1955 a h
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c2082 := derived2082 a h
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2172 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2171, some c1147, some c2169, some c119, some c7, some c819, some c2160, some c2102, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2172 : lratChecker f2172 p2172 = .success := by decide +kernel
theorem unsat2172 : Unsatisfiable (PosFin 57) f2172 := by
  apply lratCheckerSound f2172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2172
  · intro a ha; simp [p2172] at ha; subst a; trivial
  · exact checked2172
theorem derived2172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2172 := by
  apply localUnsat_implies_entails f2172 [c2171, c1147, c2169, c119, c7, c819, c2160, c2102] c2172 unsat2172 (by rfl) a
  have h0 : Entails.eval a c2171 := derived2171 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c2169 := derived2169 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c819 := derived819 a h
  have h6 : Entails.eval a c2160 := derived2160 a h
  have h7 : Entails.eval a c2102 := derived2102 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2173 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2007, some c2169, some c7, some c2171, some c1147, some c26, some c2113, some c2172, some c2094, some c1965, some c2086, some c34, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2173 : lratChecker f2173 p2173 = .success := by decide +kernel
theorem unsat2173 : Unsatisfiable (PosFin 57) f2173 := by
  apply lratCheckerSound f2173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2173
  · intro a ha; simp [p2173] at ha; subst a; trivial
  · exact checked2173
theorem derived2173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2173 := by
  apply localUnsat_implies_entails f2173 [c2007, c2169, c7, c2171, c1147, c26, c2113, c2172, c2094, c1965, c2086, c34] c2173 unsat2173 (by rfl) a
  have h0 : Entails.eval a c2007 := derived2007 a h
  have h1 : Entails.eval a c2169 := derived2169 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c2171 := derived2171 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c2113 := derived2113 a h
  have h7 : Entails.eval a c2172 := derived2172 a h
  have h8 : Entails.eval a c2094 := derived2094 a h
  have h9 : Entails.eval a c1965 := derived1965 a h
  have h10 : Entails.eval a c2086 := derived2086 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2174 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2131, some c2116, some c49, some c318, some c2115, some c2130, some c261, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p2174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2174 : lratChecker f2174 p2174 = .success := by decide +kernel
theorem unsat2174 : Unsatisfiable (PosFin 57) f2174 := by
  apply lratCheckerSound f2174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2174
  · intro a ha; simp [p2174] at ha; subst a; trivial
  · exact checked2174
theorem derived2174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2174 := by
  apply localUnsat_implies_entails f2174 [c2131, c2116, c49, c318, c2115, c2130, c261] c2174 unsat2174 (by rfl) a
  have h0 : Entails.eval a c2131 := derived2131 a h
  have h1 : Entails.eval a c2116 := derived2116 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c2115 := derived2115 a h
  have h5 : Entails.eval a c2130 := derived2130 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2175 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2115, some c206, some c207, some c49, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p2175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2175 : lratChecker f2175 p2175 = .success := by decide +kernel
theorem unsat2175 : Unsatisfiable (PosFin 57) f2175 := by
  apply lratCheckerSound f2175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2175
  · intro a ha; simp [p2175] at ha; subst a; trivial
  · exact checked2175
theorem derived2175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2175 := by
  apply localUnsat_implies_entails f2175 [c2115, c206, c207, c49] c2175 unsat2175 (by rfl) a
  have h0 : Entails.eval a c2115 := derived2115 a h
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2176 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨32, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2173, some c2143, some c1083, some c55, some c2084, some c69, some c152, some c346, some c284, some c2118, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2176 : lratChecker f2176 p2176 = .success := by decide +kernel
theorem unsat2176 : Unsatisfiable (PosFin 57) f2176 := by
  apply lratCheckerSound f2176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2176
  · intro a ha; simp [p2176] at ha; subst a; trivial
  · exact checked2176
theorem derived2176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2176 := by
  apply localUnsat_implies_entails f2176 [c2085, c2094, c2173, c2143, c1083, c55, c2084, c69, c152, c346, c284, c2118] c2176 unsat2176 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2143 := derived2143 a h
  have h4 : Entails.eval a c1083 := derived1083 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c2084 := derived2084 a h
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c2118 := derived2118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2177 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2173, some c2174, some c2077, some c2175, some c261, some c2176, some c111, some c1380, some c5, some c25, some c55, some c153, some c138, some c2081, some c2084, some c2120, some c230, some c247, some c285, some c63, some c276, some c353, some c2137, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2177 : lratChecker f2177 p2177 = .success := by decide +kernel
theorem unsat2177 : Unsatisfiable (PosFin 57) f2177 := by
  apply lratCheckerSound f2177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2177
  · intro a ha; simp [p2177] at ha; subst a; trivial
  · exact checked2177
theorem derived2177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2177 := by
  apply localUnsat_implies_entails f2177 [c2085, c2094, c2173, c2174, c2077, c2175, c261, c2176, c111, c1380, c5, c25, c55, c153, c138, c2081, c2084, c2120, c230, c247, c285, c63, c276, c353, c2137] c2177 unsat2177 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2174 := derived2174 a h
  have h4 : Entails.eval a c2077 := derived2077 a h
  have h5 : Entails.eval a c2175 := derived2175 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c2176 := derived2176 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c1380 := derived1380 a h
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c138 := h 137 (by decide)
  have h15 : Entails.eval a c2081 := derived2081 a h
  have h16 : Entails.eval a c2084 := derived2084 a h
  have h17 : Entails.eval a c2120 := derived2120 a h
  have h18 : Entails.eval a c230 := h 229 (by decide)
  have h19 : Entails.eval a c247 := h 246 (by decide)
  have h20 : Entails.eval a c285 := h 284 (by decide)
  have h21 : Entails.eval a c63 := h 62 (by decide)
  have h22 : Entails.eval a c276 := h 275 (by decide)
  have h23 : Entails.eval a c353 := h 352 (by decide)
  have h24 : Entails.eval a c2137 := derived2137 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2178 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨21, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2130, some c2116, some c2091, some c24, some c1083, some c280, some c2084, some c2118, some c156, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2178 : lratChecker f2178 p2178 = .success := by decide +kernel
theorem unsat2178 : Unsatisfiable (PosFin 57) f2178 := by
  apply lratCheckerSound f2178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2178
  · intro a ha; simp [p2178] at ha; subst a; trivial
  · exact checked2178
theorem derived2178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2178 := by
  apply localUnsat_implies_entails f2178 [c2130, c2116, c2091, c24, c1083, c280, c2084, c2118, c156] c2178 unsat2178 (by rfl) a
  have h0 : Entails.eval a c2130 := derived2130 a h
  have h1 : Entails.eval a c2116 := derived2116 a h
  have h2 : Entails.eval a c2091 := derived2091 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c1083 := derived1083 a h
  have h5 : Entails.eval a c280 := h 279 (by decide)
  have h6 : Entails.eval a c2084 := derived2084 a h
  have h7 : Entails.eval a c2118 := derived2118 a h
  have h8 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2179 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c2094, some c2173, some c2116, some c2130, some c318, some c2178, some c53, some c138, some c152, some c146, some c89, some c312, some c200, some c719, some c176, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked2179 : lratChecker f2179 p2179 = .success := by decide +kernel
theorem unsat2179 : Unsatisfiable (PosFin 57) f2179 := by
  apply lratCheckerSound f2179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2179
  · intro a ha; simp [p2179] at ha; subst a; trivial
  · exact checked2179
theorem derived2179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2179 := by
  apply localUnsat_implies_entails f2179 [c268, c2094, c2173, c2116, c2130, c318, c2178, c53, c138, c152, c146, c89, c312, c200, c719, c176] c2179 unsat2179 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2116 := derived2116 a h
  have h4 : Entails.eval a c2130 := derived2130 a h
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c2178 := derived2178 a h
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c312 := h 311 (by decide)
  have h13 : Entails.eval a c200 := h 199 (by decide)
  have h14 : Entails.eval a c719 := derived719 a h
  have h15 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2180 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2173, some c2177, some c268, some c2179, some c2077, some c2176, some c111, some c1896, some c2079, some c5, some c25, some c55, some c153, some c138, some c2084, some c2120, some c230, some c89, some c285, some c287, some c276, some c274, some c2117, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked2180 : lratChecker f2180 p2180 = .success := by decide +kernel
theorem unsat2180 : Unsatisfiable (PosFin 57) f2180 := by
  apply lratCheckerSound f2180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2180
  · intro a ha; simp [p2180] at ha; subst a; trivial
  · exact checked2180
theorem derived2180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2180 := by
  apply localUnsat_implies_entails f2180 [c2085, c2094, c2173, c2177, c268, c2179, c2077, c2176, c111, c1896, c2079, c5, c25, c55, c153, c138, c2084, c2120, c230, c89, c285, c287, c276, c274, c2117] c2180 unsat2180 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2177 := derived2177 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c2179 := derived2179 a h
  have h6 : Entails.eval a c2077 := derived2077 a h
  have h7 : Entails.eval a c2176 := derived2176 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c1896 := derived1896 a h
  have h10 : Entails.eval a c2079 := derived2079 a h
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  have h14 : Entails.eval a c153 := h 152 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c2084 := derived2084 a h
  have h17 : Entails.eval a c2120 := derived2120 a h
  have h18 : Entails.eval a c230 := h 229 (by decide)
  have h19 : Entails.eval a c89 := h 88 (by decide)
  have h20 : Entails.eval a c285 := h 284 (by decide)
  have h21 : Entails.eval a c287 := h 286 (by decide)
  have h22 : Entails.eval a c276 := h 275 (by decide)
  have h23 : Entails.eval a c274 := h 273 (by decide)
  have h24 : Entails.eval a c2117 := derived2117 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2181 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2126, some c2076, some c261, some c2077, some c2116, some c2174, some c2130, some c318, some c312, some c139, some c152, some c239, some c2098, some c135, some c200, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2181 : lratChecker f2181 p2181 = .success := by decide +kernel
theorem unsat2181 : Unsatisfiable (PosFin 57) f2181 := by
  apply lratCheckerSound f2181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2181
  · intro a ha; simp [p2181] at ha; subst a; trivial
  · exact checked2181
theorem derived2181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2181 := by
  apply localUnsat_implies_entails f2181 [c2085, c2094, c2126, c2076, c261, c2077, c2116, c2174, c2130, c318, c312, c139, c152, c239, c2098, c135, c200] c2181 unsat2181 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2126 := derived2126 a h
  have h3 : Entails.eval a c2076 := derived2076 a h
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c2077 := derived2077 a h
  have h6 : Entails.eval a c2116 := derived2116 a h
  have h7 : Entails.eval a c2174 := derived2174 a h
  have h8 : Entails.eval a c2130 := derived2130 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c312 := h 311 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  have h14 : Entails.eval a c2098 := derived2098 a h
  have h15 : Entails.eval a c135 := h 134 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2182 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c2174, some c2077, some c2175, some c1723, some c56, some c55, some c152, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2182 : lratChecker f2182 p2182 = .success := by decide +kernel
theorem unsat2182 : Unsatisfiable (PosFin 57) f2182 := by
  apply lratCheckerSound f2182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2182
  · intro a ha; simp [p2182] at ha; subst a; trivial
  · exact checked2182
theorem derived2182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2182 := by
  apply localUnsat_implies_entails f2182 [c112, c2174, c2077, c2175, c1723, c56, c55, c152] c2182 unsat2182 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c2174 := derived2174 a h
  have h2 : Entails.eval a c2077 := derived2077 a h
  have h3 : Entails.eval a c2175 := derived2175 a h
  have h4 : Entails.eval a c1723 := derived1723 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2183 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2181, some c2180, some c112, some c2182, some c268, some c2179, some c2079, some c56, some c55, some c152, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2183 : lratChecker f2183 p2183 = .success := by decide +kernel
theorem unsat2183 : Unsatisfiable (PosFin 57) f2183 := by
  apply lratCheckerSound f2183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2183
  · intro a ha; simp [p2183] at ha; subst a; trivial
  · exact checked2183
theorem derived2183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2183 := by
  apply localUnsat_implies_entails f2183 [c2085, c2094, c2181, c2180, c112, c2182, c268, c2179, c2079, c56, c55, c152] c2183 unsat2183 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2181 := derived2181 a h
  have h3 : Entails.eval a c2180 := derived2180 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c2182 := derived2182 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c2179 := derived2179 a h
  have h8 : Entails.eval a c2079 := derived2079 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2184 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2183, some c20, some c112, some c2174, some c2077, some c2175, some c261, some c2076, some c1908, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2184 : lratChecker f2184 p2184 = .success := by decide +kernel
theorem unsat2184 : Unsatisfiable (PosFin 57) f2184 := by
  apply lratCheckerSound f2184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2184
  · intro a ha; simp [p2184] at ha; subst a; trivial
  · exact checked2184
theorem derived2184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2184 := by
  apply localUnsat_implies_entails f2184 [c2085, c2094, c2183, c20, c112, c2174, c2077, c2175, c261, c2076, c1908] c2184 unsat2184 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2183 := derived2183 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c2174 := derived2174 a h
  have h6 : Entails.eval a c2077 := derived2077 a h
  have h7 : Entails.eval a c2175 := derived2175 a h
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c2076 := derived2076 a h
  have h10 : Entails.eval a c1908 := derived1908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2185 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2183, some c20, some c112, some c2184, some c268, some c1896, some c2079, some c1909, some c1908, some c2071, some c2076, some c2116, some c2130, some c49, some c312, some c707, some c139, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked2185 : lratChecker f2185 p2185 = .success := by decide +kernel
theorem unsat2185 : Unsatisfiable (PosFin 57) f2185 := by
  apply lratCheckerSound f2185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2185
  · intro a ha; simp [p2185] at ha; subst a; trivial
  · exact checked2185
theorem derived2185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2185 := by
  apply localUnsat_implies_entails f2185 [c2085, c2094, c2183, c20, c112, c2184, c268, c1896, c2079, c1909, c1908, c2071, c2076, c2116, c2130, c49, c312, c707, c139] c2185 unsat2185 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2183 := derived2183 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c2184 := derived2184 a h
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c1896 := derived1896 a h
  have h8 : Entails.eval a c2079 := derived2079 a h
  have h9 : Entails.eval a c1909 := derived1909 a h
  have h10 : Entails.eval a c1908 := derived1908 a h
  have h11 : Entails.eval a c2071 := derived2071 a h
  have h12 : Entails.eval a c2076 := derived2076 a h
  have h13 : Entails.eval a c2116 := derived2116 a h
  have h14 : Entails.eval a c2130 := derived2130 a h
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c312 := h 311 (by decide)
  have h17 : Entails.eval a c707 := derived707 a h
  have h18 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2186 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2185, some c2173, some c13, some c112, some c12, some c2124, some c2085, some c2182, some c198, some c2146, some c2090, some c203, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked2186 : lratChecker f2186 p2186 = .success := by decide +kernel
theorem unsat2186 : Unsatisfiable (PosFin 57) f2186 := by
  apply lratCheckerSound f2186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2186
  · intro a ha; simp [p2186] at ha; subst a; trivial
  · exact checked2186
theorem derived2186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2186 := by
  apply localUnsat_implies_entails f2186 [c2185, c2173, c13, c112, c12, c2124, c2085, c2182, c198, c2146, c2090, c203] c2186 unsat2186 (by rfl) a
  have h0 : Entails.eval a c2185 := derived2185 a h
  have h1 : Entails.eval a c2173 := derived2173 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c2124 := derived2124 a h
  have h6 : Entails.eval a c2085 := derived2085 a h
  have h7 : Entails.eval a c2182 := derived2182 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c2146 := derived2146 a h
  have h10 : Entails.eval a c2090 := derived2090 a h
  have h11 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2187 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2185, some c2173, some c13, some c112, some c12, some c2124, some c819, some c2186, some c268, some c2152, some c2079, some c56, some c55, some c139, some c152, some c92, some c198, some c175, some c2146, some c203, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2187 : lratChecker f2187 p2187 = .success := by decide +kernel
theorem unsat2187 : Unsatisfiable (PosFin 57) f2187 := by
  apply lratCheckerSound f2187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2187
  · intro a ha; simp [p2187] at ha; subst a; trivial
  · exact checked2187
theorem derived2187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2187 := by
  apply localUnsat_implies_entails f2187 [c2185, c2173, c13, c112, c12, c2124, c819, c2186, c268, c2152, c2079, c56, c55, c139, c152, c92, c198, c175, c2146, c203] c2187 unsat2187 (by rfl) a
  have h0 : Entails.eval a c2185 := derived2185 a h
  have h1 : Entails.eval a c2173 := derived2173 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c2124 := derived2124 a h
  have h6 : Entails.eval a c819 := derived819 a h
  have h7 : Entails.eval a c2186 := derived2186 a h
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c2152 := derived2152 a h
  have h10 : Entails.eval a c2079 := derived2079 a h
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c2146 := derived2146 a h
  have h19 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2188 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f2188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c261, some c1908, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p2188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked2188 : lratChecker f2188 p2188 = .success := by decide +kernel
theorem unsat2188 : Unsatisfiable (PosFin 57) f2188 := by
  apply lratCheckerSound f2188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2188
  · intro a ha; simp [p2188] at ha; subst a; trivial
  · exact checked2188
theorem derived2188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2188 := by
  apply localUnsat_implies_entails f2188 [c261, c1908] c2188 unsat2188 (by rfl) a
  have h0 : Entails.eval a c261 := h 260 (by decide)
  have h1 : Entails.eval a c1908 := derived1908 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c2189 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2173, some c2185, some c819, some c13, some c2124, some c112, some c12, some c2187, some c2188, some c2080, some c153, some c74, some c2113, some c2159, some c2175, some c2077, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked2189 : lratChecker f2189 p2189 = .success := by decide +kernel
theorem unsat2189 : Unsatisfiable (PosFin 57) f2189 := by
  apply lratCheckerSound f2189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2189
  · intro a ha; simp [p2189] at ha; subst a; trivial
  · exact checked2189
theorem derived2189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2189 := by
  apply localUnsat_implies_entails f2189 [c2085, c2173, c2185, c819, c13, c2124, c112, c12, c2187, c2188, c2080, c153, c74, c2113, c2159, c2175, c2077] c2189 unsat2189 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2173 := derived2173 a h
  have h2 : Entails.eval a c2185 := derived2185 a h
  have h3 : Entails.eval a c819 := derived819 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c2124 := derived2124 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c2187 := derived2187 a h
  have h9 : Entails.eval a c2188 := derived2188 a h
  have h10 : Entails.eval a c2080 := derived2080 a h
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c2113 := derived2113 a h
  have h14 : Entails.eval a c2159 := derived2159 a h
  have h15 : Entails.eval a c2175 := derived2175 a h
  have h16 : Entails.eval a c2077 := derived2077 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2190 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2104, some c3, some c23, some c1987, some c261, some c200, some c2084, some c2146, some c4, some c2114, some c156, some c2117, some c2118, some c352, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2190 : lratChecker f2190 p2190 = .success := by decide +kernel
theorem unsat2190 : Unsatisfiable (PosFin 57) f2190 := by
  apply lratCheckerSound f2190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2190
  · intro a ha; simp [p2190] at ha; subst a; trivial
  · exact checked2190
theorem derived2190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2190 := by
  apply localUnsat_implies_entails f2190 [c2085, c2104, c3, c23, c1987, c261, c200, c2084, c2146, c4, c2114, c156, c2117, c2118, c352] c2190 unsat2190 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2104 := derived2104 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c1987 := derived1987 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c2084 := derived2084 a h
  have h8 : Entails.eval a c2146 := derived2146 a h
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c2114 := derived2114 a h
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c2117 := derived2117 a h
  have h13 : Entails.eval a c2118 := derived2118 a h
  have h14 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2191 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c2189, some c2190, some c268, some c2085, some c2179, some c2176, some c2094, some c2077, some c2080, some c1896, some c2158, some c207, some c52, some c2093, some c2146, some c2134, some c2092, some c200, some c152, some c138, some c153, some c146, some c2120, some c91, some c89, some c2118, some c315, some c288, some c175, some c2110, some c284, some c285, some c366, some c63, some c69, some c2103, some c311, some c158, some c59, some c2106, some c362, some c181, some c186, some c343, some c2125, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]]
theorem checked2191 : lratChecker f2191 p2191 = .success := by decide +kernel
theorem unsat2191 : Unsatisfiable (PosFin 57) f2191 := by
  apply lratCheckerSound f2191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2191
  · intro a ha; simp [p2191] at ha; subst a; trivial
  · exact checked2191
theorem derived2191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2191 := by
  apply localUnsat_implies_entails f2191 [c2173, c2189, c2190, c268, c2085, c2179, c2176, c2094, c2077, c2080, c1896, c2158, c207, c52, c2093, c2146, c2134, c2092, c200, c152, c138, c153, c146, c2120, c91, c89, c2118, c315, c288, c175, c2110, c284, c285, c366, c63, c69, c2103, c311, c158, c59, c2106, c362, c181, c186, c343, c2125] c2191 unsat2191 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c2189 := derived2189 a h
  have h2 : Entails.eval a c2190 := derived2190 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c2085 := derived2085 a h
  have h5 : Entails.eval a c2179 := derived2179 a h
  have h6 : Entails.eval a c2176 := derived2176 a h
  have h7 : Entails.eval a c2094 := derived2094 a h
  have h8 : Entails.eval a c2077 := derived2077 a h
  have h9 : Entails.eval a c2080 := derived2080 a h
  have h10 : Entails.eval a c1896 := derived1896 a h
  have h11 : Entails.eval a c2158 := derived2158 a h
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c2093 := derived2093 a h
  have h15 : Entails.eval a c2146 := derived2146 a h
  have h16 : Entails.eval a c2134 := derived2134 a h
  have h17 : Entails.eval a c2092 := derived2092 a h
  have h18 : Entails.eval a c200 := h 199 (by decide)
  have h19 : Entails.eval a c152 := h 151 (by decide)
  have h20 : Entails.eval a c138 := h 137 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  have h22 : Entails.eval a c146 := h 145 (by decide)
  have h23 : Entails.eval a c2120 := derived2120 a h
  have h24 : Entails.eval a c91 := h 90 (by decide)
  have h25 : Entails.eval a c89 := h 88 (by decide)
  have h26 : Entails.eval a c2118 := derived2118 a h
  have h27 : Entails.eval a c315 := h 314 (by decide)
  have h28 : Entails.eval a c288 := h 287 (by decide)
  have h29 : Entails.eval a c175 := h 174 (by decide)
  have h30 : Entails.eval a c2110 := derived2110 a h
  have h31 : Entails.eval a c284 := h 283 (by decide)
  have h32 : Entails.eval a c285 := h 284 (by decide)
  have h33 : Entails.eval a c366 := h 365 (by decide)
  have h34 : Entails.eval a c63 := h 62 (by decide)
  have h35 : Entails.eval a c69 := h 68 (by decide)
  have h36 : Entails.eval a c2103 := derived2103 a h
  have h37 : Entails.eval a c311 := h 310 (by decide)
  have h38 : Entails.eval a c158 := h 157 (by decide)
  have h39 : Entails.eval a c59 := h 58 (by decide)
  have h40 : Entails.eval a c2106 := derived2106 a h
  have h41 : Entails.eval a c362 := h 361 (by decide)
  have h42 : Entails.eval a c181 := h 180 (by decide)
  have h43 : Entails.eval a c186 := h 185 (by decide)
  have h44 : Entails.eval a c343 := h 342 (by decide)
  have h45 : Entails.eval a c2125 := derived2125 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2192 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2136, some c2093, some c2095, some c156, some c2084, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked2192 : lratChecker f2192 p2192 = .success := by decide +kernel
theorem unsat2192 : Unsatisfiable (PosFin 57) f2192 := by
  apply lratCheckerSound f2192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2192
  · intro a ha; simp [p2192] at ha; subst a; trivial
  · exact checked2192
theorem derived2192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2192 := by
  apply localUnsat_implies_entails f2192 [c2136, c2093, c2095, c156, c2084] c2192 unsat2192 (by rfl) a
  have h0 : Entails.eval a c2136 := derived2136 a h
  have h1 : Entails.eval a c2093 := derived2093 a h
  have h2 : Entails.eval a c2095 := derived2095 a h
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c2084 := derived2084 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c2193 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2094, some c2173, some c2189, some c2190, some c2179, some c2192, some c55, some c138, some c2120, some c2077, some c268, some c2176, some c2191, some c230, some c89, some c285, some c287, some c315, some c146, some c286, some c200, some c239, some c176, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked2193 : lratChecker f2193 p2193 = .success := by decide +kernel
theorem unsat2193 : Unsatisfiable (PosFin 57) f2193 := by
  apply lratCheckerSound f2193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2193
  · intro a ha; simp [p2193] at ha; subst a; trivial
  · exact checked2193
theorem derived2193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2193 := by
  apply localUnsat_implies_entails f2193 [c2085, c2094, c2173, c2189, c2190, c2179, c2192, c55, c138, c2120, c2077, c268, c2176, c2191, c230, c89, c285, c287, c315, c146, c286, c200, c239, c176] c2193 unsat2193 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2094 := derived2094 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2189 := derived2189 a h
  have h4 : Entails.eval a c2190 := derived2190 a h
  have h5 : Entails.eval a c2179 := derived2179 a h
  have h6 : Entails.eval a c2192 := derived2192 a h
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c2120 := derived2120 a h
  have h10 : Entails.eval a c2077 := derived2077 a h
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c2176 := derived2176 a h
  have h13 : Entails.eval a c2191 := derived2191 a h
  have h14 : Entails.eval a c230 := h 229 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c285 := h 284 (by decide)
  have h17 : Entails.eval a c287 := h 286 (by decide)
  have h18 : Entails.eval a c315 := h 314 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c286 := h 285 (by decide)
  have h21 : Entails.eval a c200 := h 199 (by decide)
  have h22 : Entails.eval a c239 := h 238 (by decide)
  have h23 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2194 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c2189, some c2190, some c2085, some c2094, some c2179, some c2192, some c55, some c152, some c2193, some c56, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked2194 : lratChecker f2194 p2194 = .success := by decide +kernel
theorem unsat2194 : Unsatisfiable (PosFin 57) f2194 := by
  apply lratCheckerSound f2194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2194
  · intro a ha; simp [p2194] at ha; subst a; trivial
  · exact checked2194
theorem derived2194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2194 := by
  apply localUnsat_implies_entails f2194 [c2173, c2189, c2190, c2085, c2094, c2179, c2192, c55, c152, c2193, c56] c2194 unsat2194 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c2189 := derived2189 a h
  have h2 : Entails.eval a c2190 := derived2190 a h
  have h3 : Entails.eval a c2085 := derived2085 a h
  have h4 : Entails.eval a c2094 := derived2094 a h
  have h5 : Entails.eval a c2179 := derived2179 a h
  have h6 : Entails.eval a c2192 := derived2192 a h
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c2193 := derived2193 a h
  have h10 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2195 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2189, some c2085, some c2194, some c2129, some c200, some c4, some c2114, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2195 : lratChecker f2195 p2195 = .success := by decide +kernel
theorem unsat2195 : Unsatisfiable (PosFin 57) f2195 := by
  apply lratCheckerSound f2195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2195
  · intro a ha; simp [p2195] at ha; subst a; trivial
  · exact checked2195
theorem derived2195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2195 := by
  apply localUnsat_implies_entails f2195 [c2189, c2085, c2194, c2129, c200, c4, c2114] c2195 unsat2195 (by rfl) a
  have h0 : Entails.eval a c2189 := derived2189 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2194 := derived2194 a h
  have h3 : Entails.eval a c2129 := derived2129 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c2114 := derived2114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2196 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2189, some c2085, some c2173, some c2094, some c2195, some c2072, some c14, some c1685, some c59, some c70, some c2122, some c2110, some c58, some c2117, some c1963, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2196 : lratChecker f2196 p2196 = .success := by decide +kernel
theorem unsat2196 : Unsatisfiable (PosFin 57) f2196 := by
  apply lratCheckerSound f2196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2196
  · intro a ha; simp [p2196] at ha; subst a; trivial
  · exact checked2196
theorem derived2196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2196 := by
  apply localUnsat_implies_entails f2196 [c2189, c2085, c2173, c2094, c2195, c2072, c14, c1685, c59, c70, c2122, c2110, c58, c2117, c1963] c2196 unsat2196 (by rfl) a
  have h0 : Entails.eval a c2189 := derived2189 a h
  have h1 : Entails.eval a c2085 := derived2085 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c2195 := derived2195 a h
  have h5 : Entails.eval a c2072 := derived2072 a h
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c1685 := derived1685 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c2122 := derived2122 a h
  have h11 : Entails.eval a c2110 := derived2110 a h
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c2117 := derived2117 a h
  have h14 : Entails.eval a c1963 := derived1963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2197 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c2173, some c2196, some c13, some c2093, some c2146, some c2153, some c2092, some c203, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked2197 : lratChecker f2197 p2197 = .success := by decide +kernel
theorem unsat2197 : Unsatisfiable (PosFin 57) f2197 := by
  apply lratCheckerSound f2197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2197
  · intro a ha; simp [p2197] at ha; subst a; trivial
  · exact checked2197
theorem derived2197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2197 := by
  apply localUnsat_implies_entails f2197 [c268, c2173, c2196, c13, c2093, c2146, c2153, c2092, c203] c2197 unsat2197 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c2173 := derived2173 a h
  have h2 : Entails.eval a c2196 := derived2196 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c2093 := derived2093 a h
  have h5 : Entails.eval a c2146 := derived2146 a h
  have h6 : Entails.eval a c2153 := derived2153 a h
  have h7 : Entails.eval a c2092 := derived2092 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2198 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2085, some c2196, some c819, some c268, some c2173, some c2124, some c2197, some c2158, some c2189, some c2136, some c1019, some c2110, some c156, some c2081, some c2084, some c246, some c276, some c345, some c145, some c284, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked2198 : lratChecker f2198 p2198 = .success := by decide +kernel
theorem unsat2198 : Unsatisfiable (PosFin 57) f2198 := by
  apply lratCheckerSound f2198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2198
  · intro a ha; simp [p2198] at ha; subst a; trivial
  · exact checked2198
theorem derived2198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2198 := by
  apply localUnsat_implies_entails f2198 [c2085, c2196, c819, c268, c2173, c2124, c2197, c2158, c2189, c2136, c1019, c2110, c156, c2081, c2084, c246, c276, c345, c145, c284] c2198 unsat2198 (by rfl) a
  have h0 : Entails.eval a c2085 := derived2085 a h
  have h1 : Entails.eval a c2196 := derived2196 a h
  have h2 : Entails.eval a c819 := derived819 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c2173 := derived2173 a h
  have h5 : Entails.eval a c2124 := derived2124 a h
  have h6 : Entails.eval a c2197 := derived2197 a h
  have h7 : Entails.eval a c2158 := derived2158 a h
  have h8 : Entails.eval a c2189 := derived2189 a h
  have h9 : Entails.eval a c2136 := derived2136 a h
  have h10 : Entails.eval a c1019 := derived1019 a h
  have h11 : Entails.eval a c2110 := derived2110 a h
  have h12 : Entails.eval a c156 := h 155 (by decide)
  have h13 : Entails.eval a c2081 := derived2081 a h
  have h14 : Entails.eval a c2084 := derived2084 a h
  have h15 : Entails.eval a c246 := h 245 (by decide)
  have h16 : Entails.eval a c276 := h 275 (by decide)
  have h17 : Entails.eval a c345 := h 344 (by decide)
  have h18 : Entails.eval a c145 := h 144 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2199 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c2196, some c2124, some c13, some c819, some c2189, some c2101, some c2104, some c3, some c56, some c261, some c145, some c317, some c152, some c198, some c2146, some c2092, some c203, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2199 : lratChecker f2199 p2199 = .success := by decide +kernel
theorem unsat2199 : Unsatisfiable (PosFin 57) f2199 := by
  apply lratCheckerSound f2199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2199
  · intro a ha; simp [p2199] at ha; subst a; trivial
  · exact checked2199
theorem derived2199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2199 := by
  apply localUnsat_implies_entails f2199 [c2173, c2196, c2124, c13, c819, c2189, c2101, c2104, c3, c56, c261, c145, c317, c152, c198, c2146, c2092, c203] c2199 unsat2199 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c2196 := derived2196 a h
  have h2 : Entails.eval a c2124 := derived2124 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c819 := derived819 a h
  have h5 : Entails.eval a c2189 := derived2189 a h
  have h6 : Entails.eval a c2101 := derived2101 a h
  have h7 : Entails.eval a c2104 := derived2104 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c2146 := derived2146 a h
  have h16 : Entails.eval a c2092 := derived2092 a h
  have h17 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2200 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c2196, some c819, some c13, some c2124, some c2199, some c2197, some c2198, some c198, some c56, some c152, some c145, some c317, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2200 : lratChecker f2200 p2200 = .success := by decide +kernel
theorem unsat2200 : Unsatisfiable (PosFin 57) f2200 := by
  apply lratCheckerSound f2200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2200
  · intro a ha; simp [p2200] at ha; subst a; trivial
  · exact checked2200
theorem derived2200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2200 := by
  apply localUnsat_implies_entails f2200 [c2173, c2196, c819, c13, c2124, c2199, c2197, c2198, c198, c56, c152, c145, c317] c2200 unsat2200 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c2196 := derived2196 a h
  have h2 : Entails.eval a c819 := derived819 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c2124 := derived2124 a h
  have h5 : Entails.eval a c2199 := derived2199 a h
  have h6 : Entails.eval a c2197 := derived2197 a h
  have h7 : Entails.eval a c2198 := derived2198 a h
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2201 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨34, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c16, some c69, some c111, some c346, some c68, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2201 : lratChecker f2201 p2201 = .success := by decide +kernel
theorem unsat2201 : Unsatisfiable (PosFin 57) f2201 := by
  apply lratCheckerSound f2201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2201
  · intro a ha; simp [p2201] at ha; subst a; trivial
  · exact checked2201
theorem derived2201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2201 := by
  apply localUnsat_implies_entails f2201 [c2173, c16, c69, c111, c346, c68] c2201 unsat2201 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2202 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2200, some c1147, some c201, some c2094, some c198, some c2090, some c2093, some c2091, some c2173, some c210, some c715, some c214, some c261, some c2080, some c2104, some c1161, some c157, some c2201, some c112, some c56, some c2018, some c148, some c49, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2202 : lratChecker f2202 p2202 = .success := by decide +kernel
theorem unsat2202 : Unsatisfiable (PosFin 57) f2202 := by
  apply lratCheckerSound f2202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2202
  · intro a ha; simp [p2202] at ha; subst a; trivial
  · exact checked2202
theorem derived2202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2202 := by
  apply localUnsat_implies_entails f2202 [c2200, c1147, c201, c2094, c198, c2090, c2093, c2091, c2173, c210, c715, c214, c261, c2080, c2104, c1161, c157, c2201, c112, c56, c2018, c148, c49] c2202 unsat2202 (by rfl) a
  have h0 : Entails.eval a c2200 := derived2200 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c2094 := derived2094 a h
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c2090 := derived2090 a h
  have h6 : Entails.eval a c2093 := derived2093 a h
  have h7 : Entails.eval a c2091 := derived2091 a h
  have h8 : Entails.eval a c2173 := derived2173 a h
  have h9 : Entails.eval a c210 := h 209 (by decide)
  have h10 : Entails.eval a c715 := derived715 a h
  have h11 : Entails.eval a c214 := h 213 (by decide)
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c2080 := derived2080 a h
  have h14 : Entails.eval a c2104 := derived2104 a h
  have h15 : Entails.eval a c1161 := derived1161 a h
  have h16 : Entails.eval a c157 := h 156 (by decide)
  have h17 : Entails.eval a c2201 := derived2201 a h
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c2018 := derived2018 a h
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2203 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2200, some c1147, some c198, some c2091, some c2173, some c2202, some c959, some c2134, some c34, some c1674, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked2203 : lratChecker f2203 p2203 = .success := by decide +kernel
theorem unsat2203 : Unsatisfiable (PosFin 57) f2203 := by
  apply lratCheckerSound f2203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2203
  · intro a ha; simp [p2203] at ha; subst a; trivial
  · exact checked2203
theorem derived2203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2203 := by
  apply localUnsat_implies_entails f2203 [c2200, c1147, c198, c2091, c2173, c2202, c959, c2134, c34, c1674] c2203 unsat2203 (by rfl) a
  have h0 : Entails.eval a c2200 := derived2200 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c2091 := derived2091 a h
  have h4 : Entails.eval a c2173 := derived2173 a h
  have h5 : Entails.eval a c2202 := derived2202 a h
  have h6 : Entails.eval a c959 := derived959 a h
  have h7 : Entails.eval a c2134 := derived2134 a h
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c1674 := derived1674 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2204 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2200, some c1147, some c2173, some c198, some c2091, some c2093, some c2090, some c2203, some c13, some c1666, some c56, some c1665, some c145, some c2104, some c315, some c261, some c699, some c2092, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked2204 : lratChecker f2204 p2204 = .success := by decide +kernel
theorem unsat2204 : Unsatisfiable (PosFin 57) f2204 := by
  apply lratCheckerSound f2204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2204
  · intro a ha; simp [p2204] at ha; subst a; trivial
  · exact checked2204
theorem derived2204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2204 := by
  apply localUnsat_implies_entails f2204 [c2200, c1147, c2173, c198, c2091, c2093, c2090, c2203, c13, c1666, c56, c1665, c145, c2104, c315, c261, c699, c2092] c2204 unsat2204 (by rfl) a
  have h0 : Entails.eval a c2200 := derived2200 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c2091 := derived2091 a h
  have h5 : Entails.eval a c2093 := derived2093 a h
  have h6 : Entails.eval a c2090 := derived2090 a h
  have h7 : Entails.eval a c2203 := derived2203 a h
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c1666 := derived1666 a h
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c1665 := derived1665 a h
  have h12 : Entails.eval a c145 := h 144 (by decide)
  have h13 : Entails.eval a c2104 := derived2104 a h
  have h14 : Entails.eval a c315 := h 314 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c699 := derived699 a h
  have h17 : Entails.eval a c2092 := derived2092 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2205 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c2089, some c222, some c2110, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked2205 : lratChecker f2205 p2205 = .success := by decide +kernel
theorem unsat2205 : Unsatisfiable (PosFin 57) f2205 := by
  apply lratCheckerSound f2205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2205
  · intro a ha; simp [p2205] at ha; subst a; trivial
  · exact checked2205
theorem derived2205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2205 := by
  apply localUnsat_implies_entails f2205 [c162, c2089, c222, c2110] c2205 unsat2205 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c2089 := derived2089 a h
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c2110 := derived2110 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c2206 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2200, some c1147, some c2173, some c2204, some c2126, some c2124, some c261, some c2144, some c202, some c2092, some c2205, some c226, some c2118, some c2110, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked2206 : lratChecker f2206 p2206 = .success := by decide +kernel
theorem unsat2206 : Unsatisfiable (PosFin 57) f2206 := by
  apply lratCheckerSound f2206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2206
  · intro a ha; simp [p2206] at ha; subst a; trivial
  · exact checked2206
theorem derived2206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2206 := by
  apply localUnsat_implies_entails f2206 [c2200, c1147, c2173, c2204, c2126, c2124, c261, c2144, c202, c2092, c2205, c226, c2118, c2110] c2206 unsat2206 (by rfl) a
  have h0 : Entails.eval a c2200 := derived2200 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c2173 := derived2173 a h
  have h3 : Entails.eval a c2204 := derived2204 a h
  have h4 : Entails.eval a c2126 := derived2126 a h
  have h5 : Entails.eval a c2124 := derived2124 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c2144 := derived2144 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c2092 := derived2092 a h
  have h10 : Entails.eval a c2205 := derived2205 a h
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c2118 := derived2118 a h
  have h13 : Entails.eval a c2110 := derived2110 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2207 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2173, some c2200, some c1147, some c2206, some c2086, some c268, some c2094, some c13, some c2124, some c198, some c2093, some c2153, some c2097, some c2092, some c203, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked2207 : lratChecker f2207 p2207 = .success := by decide +kernel
theorem unsat2207 : Unsatisfiable (PosFin 57) f2207 := by
  apply lratCheckerSound f2207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2207
  · intro a ha; simp [p2207] at ha; subst a; trivial
  · exact checked2207
theorem derived2207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2207 := by
  apply localUnsat_implies_entails f2207 [c2173, c2200, c1147, c2206, c2086, c268, c2094, c13, c2124, c198, c2093, c2153, c2097, c2092, c203] c2207 unsat2207 (by rfl) a
  have h0 : Entails.eval a c2173 := derived2173 a h
  have h1 : Entails.eval a c2200 := derived2200 a h
  have h2 : Entails.eval a c1147 := derived1147 a h
  have h3 : Entails.eval a c2206 := derived2206 a h
  have h4 : Entails.eval a c2086 := derived2086 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c2094 := derived2094 a h
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c2124 := derived2124 a h
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c2093 := derived2093 a h
  have h11 : Entails.eval a c2153 := derived2153 a h
  have h12 : Entails.eval a c2097 := derived2097 a h
  have h13 : Entails.eval a c2092 := derived2092 a h
  have h14 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2208 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨19, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2207, some c119, some c7, some c3, some c115, some c51, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked2208 : lratChecker f2208 p2208 = .success := by decide +kernel
theorem unsat2208 : Unsatisfiable (PosFin 57) f2208 := by
  apply lratCheckerSound f2208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2208
  · intro a ha; simp [p2208] at ha; subst a; trivial
  · exact checked2208
theorem derived2208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2208 := by
  apply localUnsat_implies_entails f2208 [c2207, c119, c7, c3, c115, c51] c2208 unsat2208 (by rfl) a
  have h0 : Entails.eval a c2207 := derived2207 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2209 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2209 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2207, some c128, some c119, some c7, some c2173, some c2208, some c200, some c203, some c819, some c12, some c56, some c1024, some c2101, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2209 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2209 : lratChecker f2209 p2209 = .success := by decide +kernel
theorem unsat2209 : Unsatisfiable (PosFin 57) f2209 := by
  apply lratCheckerSound f2209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2209
  · intro a ha; simp [p2209] at ha; subst a; trivial
  · exact checked2209
theorem derived2209 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2209 := by
  apply localUnsat_implies_entails f2209 [c2207, c128, c119, c7, c2173, c2208, c200, c203, c819, c12, c56, c1024, c2101] c2209 unsat2209 (by rfl) a
  have h0 : Entails.eval a c2207 := derived2207 a h
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c2173 := derived2173 a h
  have h5 : Entails.eval a c2208 := derived2208 a h
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c819 := derived819 a h
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c1024 := derived1024 a h
  have h12 : Entails.eval a c2101 := derived2101 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2210 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2210 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2116, some c53, some c91, some c24, some c1083, some c2132, some c68, some c280, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2210 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked2210 : lratChecker f2210 p2210 = .success := by decide +kernel
theorem unsat2210 : Unsatisfiable (PosFin 57) f2210 := by
  apply lratCheckerSound f2210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2210
  · intro a ha; simp [p2210] at ha; subst a; trivial
  · exact checked2210
theorem derived2210 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2210 := by
  apply localUnsat_implies_entails f2210 [c2116, c53, c91, c24, c1083, c2132, c68, c280] c2210 unsat2210 (by rfl) a
  have h0 : Entails.eval a c2116 := derived2116 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c1083 := derived1083 a h
  have h5 : Entails.eval a c2132 := derived2132 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2211 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2211 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2080, some c1952, some c153, some c2117, some c68, some c74, some c350, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2211 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked2211 : lratChecker f2211 p2211 = .success := by decide +kernel
theorem unsat2211 : Unsatisfiable (PosFin 57) f2211 := by
  apply lratCheckerSound f2211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2211
  · intro a ha; simp [p2211] at ha; subst a; trivial
  · exact checked2211
theorem derived2211 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2211 := by
  apply localUnsat_implies_entails f2211 [c2080, c1952, c153, c2117, c68, c74, c350] c2211 unsat2211 (by rfl) a
  have h0 : Entails.eval a c2080 := derived2080 a h
  have h1 : Entails.eval a c1952 := derived1952 a h
  have h2 : Entails.eval a c153 := h 152 (by decide)
  have h3 : Entails.eval a c2117 := derived2117 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2212 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2212 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2207, some c119, some c7, some c2173, some c2192, some c56, some c2091, some c128, some c200, some c2094, some c2209, some c1024, some c51, some c1389, some c146, some c135, some c2210, some c18, some c2211, some c2154, some c2084, some c68, some c153, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p2212 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked2212 : lratChecker f2212 p2212 = .success := by decide +kernel
theorem unsat2212 : Unsatisfiable (PosFin 57) f2212 := by
  apply lratCheckerSound f2212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2212
  · intro a ha; simp [p2212] at ha; subst a; trivial
  · exact checked2212
theorem derived2212 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2212 := by
  apply localUnsat_implies_entails f2212 [c2207, c119, c7, c2173, c2192, c56, c2091, c128, c200, c2094, c2209, c1024, c51, c1389, c146, c135, c2210, c18, c2211, c2154, c2084, c68, c153] c2212 unsat2212 (by rfl) a
  have h0 : Entails.eval a c2207 := derived2207 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c2173 := derived2173 a h
  have h4 : Entails.eval a c2192 := derived2192 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c2091 := derived2091 a h
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c2094 := derived2094 a h
  have h10 : Entails.eval a c2209 := derived2209 a h
  have h11 : Entails.eval a c1024 := derived1024 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c1389 := derived1389 a h
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c135 := h 134 (by decide)
  have h16 : Entails.eval a c2210 := derived2210 a h
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c2211 := derived2211 a h
  have h19 : Entails.eval a c2154 := derived2154 a h
  have h20 : Entails.eval a c2084 := derived2084 a h
  have h21 : Entails.eval a c68 := h 67 (by decide)
  have h22 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c2213 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨28, by decide⟩, false), (⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, false), (⟨12, by decide⟩, false), (⟨20, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f2213 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1931, some c200, some c2094, some c2115, some c1952, some c53, some c2117, some c146, some c158, some c277, some c58, some c59, some c2122, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p2213 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked2213 : lratChecker f2213 p2213 = .success := by decide +kernel
theorem unsat2213 : Unsatisfiable (PosFin 57) f2213 := by
  apply lratCheckerSound f2213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p2213
  · intro a ha; simp [p2213] at ha; subst a; trivial
  · exact checked2213
theorem derived2213 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c2213 := by
  apply localUnsat_implies_entails f2213 [c1931, c200, c2094, c2115, c1952, c53, c2117, c146, c158, c277, c58, c59, c2122] c2213 unsat2213 (by rfl) a
  have h0 : Entails.eval a c1931 := derived1931 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c2094 := derived2094 a h
  have h3 : Entails.eval a c2115 := derived2115 a h
  have h4 : Entails.eval a c1952 := derived1952 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c2117 := derived2117 a h
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c277 := h 276 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c2122 := derived2122 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived2213

end CochromaticTwenty.Certificates.B16_0_2Enumerating
