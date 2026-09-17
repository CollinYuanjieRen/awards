import MerLeanExperiment.Certificates.Z12Direct_4_1_4.Inputs

/-! Generated from the actual pinned z12direct_4_1_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_1_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c41 : DefaultClause 29 := directClause [(⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f41 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c8, some c34, some c10, some c6, some c36, some c35, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p41 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked41 : lratChecker f41 p41 = .success := by decide +kernel
theorem unsat41 : Unsatisfiable (PosFin 29) f41 := by
  apply lratCheckerSound f41 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p41
  · intro a ha; simp [p41] at ha; subst a; trivial
  · exact checked41
theorem derived41 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c41 := by
  apply localUnsat_implies_entails f41 [c8, c34, c10, c6, c36, c35] c41 unsat41 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c42 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f42 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c25, some c30, some c4, some c31, some c18, some c13, some c14, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p42 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked42 : lratChecker f42 p42 = .success := by decide +kernel
theorem unsat42 : Unsatisfiable (PosFin 29) f42 := by
  apply lratCheckerSound f42 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p42
  · intro a ha; simp [p42] at ha; subst a; trivial
  · exact checked42
theorem derived42 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c42 := by
  apply localUnsat_implies_entails f42 [c25, c30, c4, c31, c18, c13, c14] c42 unsat42 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c43 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f43 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c8, some c34, some c29, some c32, some c36, some c3, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p43 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked43 : lratChecker f43 p43 = .success := by decide +kernel
theorem unsat43 : Unsatisfiable (PosFin 29) f43 := by
  apply lratCheckerSound f43 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p43
  · intro a ha; simp [p43] at ha; subst a; trivial
  · exact checked43
theorem derived43 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c43 := by
  apply localUnsat_implies_entails f43 [c8, c34, c29, c32, c36, c3] c43 unsat43 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c44 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f44 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c25, some c30, some c5, some c43, some c41, some c42, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p44 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked44 : lratChecker f44 p44 = .success := by decide +kernel
theorem unsat44 : Unsatisfiable (PosFin 29) f44 := by
  apply lratCheckerSound f44 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p44
  · intro a ha; simp [p44] at ha; subst a; trivial
  · exact checked44
theorem derived44 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c44 := by
  apply localUnsat_implies_entails f44 [c25, c30, c5, c43, c41, c42] c44 unsat44 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c43 := derived43 a h
  have h4 : Entails.eval a c41 := derived41 a h
  have h5 : Entails.eval a c42 := derived42 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c45 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f45 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c12, some c14, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p45 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked45 : lratChecker f45 p45 = .success := by decide +kernel
theorem unsat45 : Unsatisfiable (PosFin 29) f45 := by
  apply lratCheckerSound f45 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p45
  · intro a ha; simp [p45] at ha; subst a; trivial
  · exact checked45
theorem derived45 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c45 := by
  apply localUnsat_implies_entails f45 [c12, c14] c45 unsat45 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c46 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f46 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c25, some c30, some c34, some c29, some c5, some c8, some c43, some c4, some c18, some c44, some c7, some c23, some c45, some c22, some c31, some c27, some c19, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p46 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked46 : lratChecker f46 p46 = .success := by decide +kernel
theorem unsat46 : Unsatisfiable (PosFin 29) f46 := by
  apply lratCheckerSound f46 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p46
  · intro a ha; simp [p46] at ha; subst a; trivial
  · exact checked46
theorem derived46 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c46 := by
  apply localUnsat_implies_entails f46 [c25, c30, c34, c29, c5, c8, c43, c4, c18, c44, c7, c23, c45, c22, c31, c27, c19] c46 unsat46 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c43 := derived43 a h
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c44 := derived44 a h
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c45 := derived45 a h
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c27 := h 26 (by decide)
  have h16 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c47 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f47 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c46, some c9, some c37, some c25, some c39, some c28, some c2, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p47 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked47 : lratChecker f47 p47 = .success := by decide +kernel
theorem unsat47 : Unsatisfiable (PosFin 29) f47 := by
  apply lratCheckerSound f47 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p47
  · intro a ha; simp [p47] at ha; subst a; trivial
  · exact checked47
theorem derived47 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c47 := by
  apply localUnsat_implies_entails f47 [c46, c9, c37, c25, c39, c28, c2] c47 unsat47 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c48 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f48 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c25, some c30, some c47, some c4, some c43, some c46, some c9, some c37, some c15, some c21, some c2, some c20, some c33, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p48 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked48 : lratChecker f48 p48 = .success := by decide +kernel
theorem unsat48 : Unsatisfiable (PosFin 29) f48 := by
  apply lratCheckerSound f48 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p48
  · intro a ha; simp [p48] at ha; subst a; trivial
  · exact checked48
theorem derived48 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c48 := by
  apply localUnsat_implies_entails f48 [c25, c30, c47, c4, c43, c46, c9, c37, c15, c21, c2, c20, c33] c48 unsat48 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c47 := derived47 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c43 := derived43 a h
  have h5 : Entails.eval a c46 := derived46 a h
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c49 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f49 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c25, some c30, some c29, some c46, some c9, some c47, some c4, some c17, some c48, some c26, some c1, some c16, some c11, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p49 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked49 : lratChecker f49 p49 = .success := by decide +kernel
theorem unsat49 : Unsatisfiable (PosFin 29) f49 := by
  apply lratCheckerSound f49 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p49
  · intro a ha; simp [p49] at ha; subst a; trivial
  · exact checked49
theorem derived49 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c49 := by
  apply localUnsat_implies_entails f49 [c25, c30, c29, c46, c9, c47, c4, c17, c48, c26, c1, c16, c11] c49 unsat49 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c46 := derived46 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c47 := derived47 a h
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c48 := derived48 a h
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c50 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f50 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c49, some c24, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p50 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked50 : lratChecker f50 p50 = .success := by decide +kernel
theorem unsat50 : Unsatisfiable (PosFin 29) f50 := by
  apply lratCheckerSound f50 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p50
  · intro a ha; simp [p50] at ha; subst a; trivial
  · exact checked50
theorem derived50 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c50 := by
  apply localUnsat_implies_entails f50 [c49, c24] c50 unsat50 (by rfl) a
  have h0 : Entails.eval a c49 := derived49 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c51 : DefaultClause 29 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f51 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c49, some c38, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p51 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked51 : lratChecker f51 p51 = .success := by decide +kernel
theorem unsat51 : Unsatisfiable (PosFin 29) f51 := by
  apply lratCheckerSound f51 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p51
  · intro a ha; simp [p51] at ha; subst a; trivial
  · exact checked51
theorem derived51 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c51 := by
  apply localUnsat_implies_entails f51 [c49, c38] c51 unsat51 (by rfl) a
  have h0 : Entails.eval a c49 := derived49 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c52 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f52 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c51, some c50, some c40]
def p52 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked52 : lratChecker f52 p52 = .success := by decide +kernel
theorem unsat52 : Unsatisfiable (PosFin 29) f52 := by
  apply lratCheckerSound f52 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p52
  · intro a ha; simp [p52] at ha; subst a; trivial
  · exact checked52
theorem derived52 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c52 := by
  apply localUnsat_implies_entails f52 [c51, c50, c40] c52 unsat52 (by rfl) a
  have h0 : Entails.eval a c51 := derived51 a h
  have h1 : Entails.eval a c50 := derived50 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived52

end CochromaticTwenty.Certificates.Z12Direct_4_1_4
