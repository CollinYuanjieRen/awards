import MerLeanExperiment.Certificates.Z12Direct_5_2_9.Inputs

/-! Generated from the actual pinned z12direct_5_2_9-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_2_9
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c38 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f38 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c10, some c14, some c16, some c2, some c22, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p38 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked38 : lratChecker f38 p38 = .success := by decide +kernel
theorem unsat38 : Unsatisfiable (PosFin 31) f38 := by
  apply lratCheckerSound f38 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p38
  · intro a ha; simp [p38] at ha; subst a; trivial
  · exact checked38
theorem derived38 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c38 := by
  apply localUnsat_implies_entails f38 [c10, c14, c16, c2, c22] c38 unsat38 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c39 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f39 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c38, some c10, some c3, some c4, some c27, some c33, some c20, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p39 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked39 : lratChecker f39 p39 = .success := by decide +kernel
theorem unsat39 : Unsatisfiable (PosFin 31) f39 := by
  apply lratCheckerSound f39 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p39
  · intro a ha; simp [p39] at ha; subst a; trivial
  · exact checked39
theorem derived39 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c39 := by
  apply localUnsat_implies_entails f39 [c38, c10, c3, c4, c27, c33, c20] c39 unsat39 (by rfl) a
  have h0 : Entails.eval a c38 := derived38 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c40 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f40 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c38, some c10, some c6, some c17, some c28, some c32, some c36, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p40 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked40 : lratChecker f40 p40 = .success := by decide +kernel
theorem unsat40 : Unsatisfiable (PosFin 31) f40 := by
  apply lratCheckerSound f40 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p40
  · intro a ha; simp [p40] at ha; subst a; trivial
  · exact checked40
theorem derived40 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c40 := by
  apply localUnsat_implies_entails f40 [c38, c10, c6, c17, c28, c32, c36] c40 unsat40 (by rfl) a
  have h0 : Entails.eval a c38 := derived38 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c41 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f41 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c10, some c38, some c40, some c39, some c8, some c18, some c34, some c26, some c29, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p41 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked41 : lratChecker f41 p41 = .success := by decide +kernel
theorem unsat41 : Unsatisfiable (PosFin 31) f41 := by
  apply lratCheckerSound f41 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p41
  · intro a ha; simp [p41] at ha; subst a; trivial
  · exact checked41
theorem derived41 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c41 := by
  apply localUnsat_implies_entails f41 [c10, c38, c40, c39, c8, c18, c34, c26, c29] c41 unsat41 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c38 := derived38 a h
  have h2 : Entails.eval a c40 := derived40 a h
  have h3 : Entails.eval a c39 := derived39 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c42 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f42 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c15, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p42 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked42 : lratChecker f42 p42 = .success := by decide +kernel
theorem unsat42 : Unsatisfiable (PosFin 31) f42 := by
  apply lratCheckerSound f42 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p42
  · intro a ha; simp [p42] at ha; subst a; trivial
  · exact checked42
theorem derived42 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c42 := by
  apply localUnsat_implies_entails f42 [c41, c15] c42 unsat42 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c43 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f43 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c12, some c18, some c34, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p43 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked43 : lratChecker f43 p43 = .success := by decide +kernel
theorem unsat43 : Unsatisfiable (PosFin 31) f43 := by
  apply lratCheckerSound f43 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p43
  · intro a ha; simp [p43] at ha; subst a; trivial
  · exact checked43
theorem derived43 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c43 := by
  apply localUnsat_implies_entails f43 [c41, c12, c18, c34] c43 unsat43 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c44 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f44 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c42, some c23, some c43, some c7, some c8, some c1, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p44 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked44 : lratChecker f44 p44 = .success := by decide +kernel
theorem unsat44 : Unsatisfiable (PosFin 31) f44 := by
  apply lratCheckerSound f44 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p44
  · intro a ha; simp [p44] at ha; subst a; trivial
  · exact checked44
theorem derived44 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c44 := by
  apply localUnsat_implies_entails f44 [c41, c42, c23, c43, c7, c8, c1] c44 unsat44 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c42 := derived42 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c43 := derived43 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c45 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f45 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c42, some c41, some c23, some c44, some c9, some c11, some c17, some c28, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p45 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked45 : lratChecker f45 p45 = .success := by decide +kernel
theorem unsat45 : Unsatisfiable (PosFin 31) f45 := by
  apply lratCheckerSound f45 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p45
  · intro a ha; simp [p45] at ha; subst a; trivial
  · exact checked45
theorem derived45 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c45 := by
  apply localUnsat_implies_entails f45 [c42, c41, c23, c44, c9, c11, c17, c28] c45 unsat45 (by rfl) a
  have h0 : Entails.eval a c42 := derived42 a h
  have h1 : Entails.eval a c41 := derived41 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c44 := derived44 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c46 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f46 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c42, some c23, some c44, some c9, some c45, some c5, some c6, some c1, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p46 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked46 : lratChecker f46 p46 = .success := by decide +kernel
theorem unsat46 : Unsatisfiable (PosFin 31) f46 := by
  apply lratCheckerSound f46 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p46
  · intro a ha; simp [p46] at ha; subst a; trivial
  · exact checked46
theorem derived46 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c46 := by
  apply localUnsat_implies_entails f46 [c41, c42, c23, c44, c9, c45, c5, c6, c1] c46 unsat46 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c42 := derived42 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c44 := derived44 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c45 := derived45 a h
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c47 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f47 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c46, some c16, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p47 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked47 : lratChecker f47 p47 = .success := by decide +kernel
theorem unsat47 : Unsatisfiable (PosFin 31) f47 := by
  apply lratCheckerSound f47 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p47
  · intro a ha; simp [p47] at ha; subst a; trivial
  · exact checked47
theorem derived47 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c47 := by
  apply localUnsat_implies_entails f47 [c46, c16] c47 unsat47 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c48 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f48 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c46, some c41, some c31, some c35, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p48 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked48 : lratChecker f48 p48 = .success := by decide +kernel
theorem unsat48 : Unsatisfiable (PosFin 31) f48 := by
  apply lratCheckerSound f48 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p48
  · intro a ha; simp [p48] at ha; subst a; trivial
  · exact checked48
theorem derived48 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c48 := by
  apply localUnsat_implies_entails f48 [c46, c41, c31, c35] c48 unsat48 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c41 := derived41 a h
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c49 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f49 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c11, some c24, some c48, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p49 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked49 : lratChecker f49 p49 = .success := by decide +kernel
theorem unsat49 : Unsatisfiable (PosFin 31) f49 := by
  apply lratCheckerSound f49 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p49
  · intro a ha; simp [p49] at ha; subst a; trivial
  · exact checked49
theorem derived49 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c49 := by
  apply localUnsat_implies_entails f49 [c41, c11, c24, c48] c49 unsat49 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c48 := derived48 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c50 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f50 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c47, some c5, some c49, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p50 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked50 : lratChecker f50 p50 = .success := by decide +kernel
theorem unsat50 : Unsatisfiable (PosFin 31) f50 := by
  apply lratCheckerSound f50 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p50
  · intro a ha; simp [p50] at ha; subst a; trivial
  · exact checked50
theorem derived50 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c50 := by
  apply localUnsat_implies_entails f50 [c41, c47, c5, c49] c50 unsat50 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c47 := derived47 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c49 := derived49 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c51 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f51 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c47, some c50, some c48, some c21, some c37, some c13, some c25, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p51 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked51 : lratChecker f51 p51 = .success := by decide +kernel
theorem unsat51 : Unsatisfiable (PosFin 31) f51 := by
  apply lratCheckerSound f51 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p51
  · intro a ha; simp [p51] at ha; subst a; trivial
  · exact checked51
theorem derived51 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c51 := by
  apply localUnsat_implies_entails f51 [c47, c50, c48, c21, c37, c13, c25] c51 unsat51 (by rfl) a
  have h0 : Entails.eval a c47 := derived47 a h
  have h1 : Entails.eval a c50 := derived50 a h
  have h2 : Entails.eval a c48 := derived48 a h
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c52 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f52 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c51, some c47, some c50, some c19, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p52 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked52 : lratChecker f52 p52 = .success := by decide +kernel
theorem unsat52 : Unsatisfiable (PosFin 31) f52 := by
  apply lratCheckerSound f52 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p52
  · intro a ha; simp [p52] at ha; subst a; trivial
  · exact checked52
theorem derived52 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c52 := by
  apply localUnsat_implies_entails f52 [c51, c47, c50, c19] c52 unsat52 (by rfl) a
  have h0 : Entails.eval a c51 := derived51 a h
  have h1 : Entails.eval a c47 := derived47 a h
  have h2 : Entails.eval a c50 := derived50 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c53 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f53 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c51, some c52, some c41, some c30, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p53 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked53 : lratChecker f53 p53 = .success := by decide +kernel
theorem unsat53 : Unsatisfiable (PosFin 31) f53 := by
  apply lratCheckerSound f53 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p53
  · intro a ha; simp [p53] at ha; subst a; trivial
  · exact checked53
theorem derived53 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c53 := by
  apply localUnsat_implies_entails f53 [c51, c52, c41, c30] c53 unsat53 (by rfl) a
  have h0 : Entails.eval a c51 := derived51 a h
  have h1 : Entails.eval a c52 := derived52 a h
  have h2 : Entails.eval a c41 := derived41 a h
  have h3 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c54 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f54 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c52, some c47, some c41, some c7, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p54 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked54 : lratChecker f54 p54 = .success := by decide +kernel
theorem unsat54 : Unsatisfiable (PosFin 31) f54 := by
  apply lratCheckerSound f54 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p54
  · intro a ha; simp [p54] at ha; subst a; trivial
  · exact checked54
theorem derived54 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c54 := by
  apply localUnsat_implies_entails f54 [c52, c47, c41, c7] c54 unsat54 (by rfl) a
  have h0 : Entails.eval a c52 := derived52 a h
  have h1 : Entails.eval a c47 := derived47 a h
  have h2 : Entails.eval a c41 := derived41 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c55 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f55 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c53, some c54, some c52, some c41, some c12]
def p55 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked55 : lratChecker f55 p55 = .success := by decide +kernel
theorem unsat55 : Unsatisfiable (PosFin 31) f55 := by
  apply lratCheckerSound f55 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p55
  · intro a ha; simp [p55] at ha; subst a; trivial
  · exact checked55
theorem derived55 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c55 := by
  apply localUnsat_implies_entails f55 [c53, c54, c52, c41, c12] c55 unsat55 (by rfl) a
  have h0 : Entails.eval a c53 := derived53 a h
  have h1 : Entails.eval a c54 := derived54 a h
  have h2 : Entails.eval a c52 := derived52 a h
  have h3 : Entails.eval a c41 := derived41 a h
  have h4 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived55

end CochromaticTwenty.Certificates.Z12Direct_5_2_9
