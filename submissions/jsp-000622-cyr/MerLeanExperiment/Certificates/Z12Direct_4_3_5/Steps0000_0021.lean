import MerLeanExperiment.Certificates.Z12Direct_4_3_5.Inputs

/-! Generated from the actual pinned z12direct_4_3_5-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_5
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c42 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f42 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c31, some c23, some c30, some c6, some c22, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p42 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked42 : lratChecker f42 p42 = .success := by decide +kernel
theorem unsat42 : Unsatisfiable (PosFin 29) f42 := by
  apply lratCheckerSound f42 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p42
  · intro a ha; simp [p42] at ha; subst a; trivial
  · exact checked42
theorem derived42 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c42 := by
  apply localUnsat_implies_entails f42 [c31, c23, c30, c6, c22] c42 unsat42 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c43 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f43 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c5, some c29, some c20, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p43 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked43 : lratChecker f43 p43 = .success := by decide +kernel
theorem unsat43 : Unsatisfiable (PosFin 29) f43 := by
  apply lratCheckerSound f43 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p43
  · intro a ha; simp [p43] at ha; subst a; trivial
  · exact checked43
theorem derived43 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c43 := by
  apply localUnsat_implies_entails f43 [c5, c29, c20] c43 unsat43 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c44 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f44 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c42, some c31, some c23, some c43, some c10, some c8, some c15, some c21, some c39, some c37, some c12, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p44 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked44 : lratChecker f44 p44 = .success := by decide +kernel
theorem unsat44 : Unsatisfiable (PosFin 29) f44 := by
  apply lratCheckerSound f44 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p44
  · intro a ha; simp [p44] at ha; subst a; trivial
  · exact checked44
theorem derived44 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c44 := by
  apply localUnsat_implies_entails f44 [c42, c31, c23, c43, c10, c8, c15, c21, c39, c37, c12] c44 unsat44 (by rfl) a
  have h0 : Entails.eval a c42 := derived42 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c43 := derived43 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c45 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f45 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c31, some c23, some c42, some c15, some c43, some c8, some c10, some c13, some c44, some c36, some c19, some c37, some c3, some c4, some c1, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p45 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked45 : lratChecker f45 p45 = .success := by decide +kernel
theorem unsat45 : Unsatisfiable (PosFin 29) f45 := by
  apply lratCheckerSound f45 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p45
  · intro a ha; simp [p45] at ha; subst a; trivial
  · exact checked45
theorem derived45 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c45 := by
  apply localUnsat_implies_entails f45 [c31, c23, c42, c15, c43, c8, c10, c13, c44, c36, c19, c37, c3, c4, c1] c45 unsat45 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c42 := derived42 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c43 := derived43 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c44 := derived44 a h
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c46 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f46 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c45, some c17, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p46 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked46 : lratChecker f46 p46 = .success := by decide +kernel
theorem unsat46 : Unsatisfiable (PosFin 29) f46 := by
  apply lratCheckerSound f46 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p46
  · intro a ha; simp [p46] at ha; subst a; trivial
  · exact checked46
theorem derived46 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c46 := by
  apply localUnsat_implies_entails f46 [c45, c17] c46 unsat46 (by rfl) a
  have h0 : Entails.eval a c45 := derived45 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c47 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f47 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c3, some c4, some c1, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p47 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked47 : lratChecker f47 p47 = .success := by decide +kernel
theorem unsat47 : Unsatisfiable (PosFin 29) f47 := by
  apply lratCheckerSound f47 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p47
  · intro a ha; simp [p47] at ha; subst a; trivial
  · exact checked47
theorem derived47 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c47 := by
  apply localUnsat_implies_entails f47 [c3, c4, c1] c47 unsat47 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c48 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f48 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c47, some c29, some c36, some c14, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p48 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked48 : lratChecker f48 p48 = .success := by decide +kernel
theorem unsat48 : Unsatisfiable (PosFin 29) f48 := by
  apply lratCheckerSound f48 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p48
  · intro a ha; simp [p48] at ha; subst a; trivial
  · exact checked48
theorem derived48 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c48 := by
  apply localUnsat_implies_entails f48 [c47, c29, c36, c14] c48 unsat48 (by rfl) a
  have h0 : Entails.eval a c47 := derived47 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c49 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f49 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c46, some c45, some c18, some c32, some c28, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p49 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked49 : lratChecker f49 p49 = .success := by decide +kernel
theorem unsat49 : Unsatisfiable (PosFin 29) f49 := by
  apply lratCheckerSound f49 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p49
  · intro a ha; simp [p49] at ha; subst a; trivial
  · exact checked49
theorem derived49 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c49 := by
  apply localUnsat_implies_entails f49 [c46, c45, c18, c32, c28] c49 unsat49 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c45 := derived45 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c50 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f50 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c45, some c48, some c9, some c33, some c28, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p50 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked50 : lratChecker f50 p50 = .success := by decide +kernel
theorem unsat50 : Unsatisfiable (PosFin 29) f50 := by
  apply lratCheckerSound f50 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p50
  · intro a ha; simp [p50] at ha; subst a; trivial
  · exact checked50
theorem derived50 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c50 := by
  apply localUnsat_implies_entails f50 [c45, c48, c9, c33, c28] c50 unsat50 (by rfl) a
  have h0 : Entails.eval a c45 := derived45 a h
  have h1 : Entails.eval a c48 := derived48 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c51 : DefaultClause 29 := directClause [(⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f51 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c45, some c9, some c35, some c28, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p51 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked51 : lratChecker f51 p51 = .success := by decide +kernel
theorem unsat51 : Unsatisfiable (PosFin 29) f51 := by
  apply lratCheckerSound f51 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p51
  · intro a ha; simp [p51] at ha; subst a; trivial
  · exact checked51
theorem derived51 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c51 := by
  apply localUnsat_implies_entails f51 [c45, c9, c35, c28] c51 unsat51 (by rfl) a
  have h0 : Entails.eval a c45 := derived45 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c52 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f52 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c46, some c30, some c2, some c51, some c37, some c18, some c34, some c28, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p52 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked52 : lratChecker f52 p52 = .success := by decide +kernel
theorem unsat52 : Unsatisfiable (PosFin 29) f52 := by
  apply lratCheckerSound f52 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p52
  · intro a ha; simp [p52] at ha; subst a; trivial
  · exact checked52
theorem derived52 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c52 := by
  apply localUnsat_implies_entails f52 [c46, c30, c2, c51, c37, c18, c34, c28] c52 unsat52 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c51 := derived51 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c53 : DefaultClause 29 := directClause [(⟨27, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f53 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c52, some c21, some c49, some c50, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p53 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked53 : lratChecker f53 p53 = .success := by decide +kernel
theorem unsat53 : Unsatisfiable (PosFin 29) f53 := by
  apply lratCheckerSound f53 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p53
  · intro a ha; simp [p53] at ha; subst a; trivial
  · exact checked53
theorem derived53 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c53 := by
  apply localUnsat_implies_entails f53 [c52, c21, c49, c50] c53 unsat53 (by rfl) a
  have h0 : Entails.eval a c52 := derived52 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c49 := derived49 a h
  have h3 : Entails.eval a c50 := derived50 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c54 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f54 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c45, some c50, some c7, some c32, some c28, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p54 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked54 : lratChecker f54 p54 = .success := by decide +kernel
theorem unsat54 : Unsatisfiable (PosFin 29) f54 := by
  apply lratCheckerSound f54 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p54
  · intro a ha; simp [p54] at ha; subst a; trivial
  · exact checked54
theorem derived54 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c54 := by
  apply localUnsat_implies_entails f54 [c45, c50, c7, c32, c28] c54 unsat54 (by rfl) a
  have h0 : Entails.eval a c45 := derived45 a h
  have h1 : Entails.eval a c50 := derived50 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c55 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f55 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c21, some c54, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p55 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked55 : lratChecker f55 p55 = .success := by decide +kernel
theorem unsat55 : Unsatisfiable (PosFin 29) f55 := by
  apply lratCheckerSound f55 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p55
  · intro a ha; simp [p55] at ha; subst a; trivial
  · exact checked55
theorem derived55 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c55 := by
  apply localUnsat_implies_entails f55 [c21, c54] c55 unsat55 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c54 := derived54 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c56 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f56 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c46, some c55, some c30, some c15, some c53, some c2, some c51, some c40, some c25, some c26, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p56 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked56 : lratChecker f56 p56 = .success := by decide +kernel
theorem unsat56 : Unsatisfiable (PosFin 29) f56 := by
  apply lratCheckerSound f56 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p56
  · intro a ha; simp [p56] at ha; subst a; trivial
  · exact checked56
theorem derived56 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c56 := by
  apply localUnsat_implies_entails f56 [c46, c55, c30, c15, c53, c2, c51, c40, c25, c26] c56 unsat56 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c55 := derived55 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c53 := derived53 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c51 := derived51 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c57 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f57 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c56, some c23, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p57 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked57 : lratChecker f57 p57 = .success := by decide +kernel
theorem unsat57 : Unsatisfiable (PosFin 29) f57 := by
  apply lratCheckerSound f57 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p57
  · intro a ha; simp [p57] at ha; subst a; trivial
  · exact checked57
theorem derived57 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c57 := by
  apply localUnsat_implies_entails f57 [c56, c23] c57 unsat57 (by rfl) a
  have h0 : Entails.eval a c56 := derived56 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c58 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f58 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c46, some c57, some c30, some c2, some c16, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p58 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked58 : lratChecker f58 p58 = .success := by decide +kernel
theorem unsat58 : Unsatisfiable (PosFin 29) f58 := by
  apply lratCheckerSound f58 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p58
  · intro a ha; simp [p58] at ha; subst a; trivial
  · exact checked58
theorem derived58 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c58 := by
  apply localUnsat_implies_entails f58 [c46, c57, c30, c2, c16] c58 unsat58 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c57 := derived57 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c59 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f59 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c58, some c21, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p59 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked59 : lratChecker f59 p59 = .success := by decide +kernel
theorem unsat59 : Unsatisfiable (PosFin 29) f59 := by
  apply lratCheckerSound f59 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p59
  · intro a ha; simp [p59] at ha; subst a; trivial
  · exact checked59
theorem derived59 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c59 := by
  apply localUnsat_implies_entails f59 [c58, c21] c59 unsat59 (by rfl) a
  have h0 : Entails.eval a c58 := derived58 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c60 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f60 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c56, some c58, some c59, some c57, some c46, some c45, some c38, some c11, some c24, some c41, some c27, some c9, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p60 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked60 : lratChecker f60 p60 = .success := by decide +kernel
theorem unsat60 : Unsatisfiable (PosFin 29) f60 := by
  apply lratCheckerSound f60 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p60
  · intro a ha; simp [p60] at ha; subst a; trivial
  · exact checked60
theorem derived60 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c60 := by
  apply localUnsat_implies_entails f60 [c56, c58, c59, c57, c46, c45, c38, c11, c24, c41, c27, c9] c60 unsat60 (by rfl) a
  have h0 : Entails.eval a c56 := derived56 a h
  have h1 : Entails.eval a c58 := derived58 a h
  have h2 : Entails.eval a c59 := derived59 a h
  have h3 : Entails.eval a c57 := derived57 a h
  have h4 : Entails.eval a c46 := derived46 a h
  have h5 : Entails.eval a c45 := derived45 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c61 : DefaultClause 29 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f61 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c60, some c45, some c7, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p61 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked61 : lratChecker f61 p61 = .success := by decide +kernel
theorem unsat61 : Unsatisfiable (PosFin 29) f61 := by
  apply lratCheckerSound f61 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p61
  · intro a ha; simp [p61] at ha; subst a; trivial
  · exact checked61
theorem derived61 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c61 := by
  apply localUnsat_implies_entails f61 [c60, c45, c7] c61 unsat61 (by rfl) a
  have h0 : Entails.eval a c60 := derived60 a h
  have h1 : Entails.eval a c45 := derived45 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c62 : DefaultClause 29 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f62 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c60, some c58, some c45, some c32, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p62 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked62 : lratChecker f62 p62 = .success := by decide +kernel
theorem unsat62 : Unsatisfiable (PosFin 29) f62 := by
  apply lratCheckerSound f62 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p62
  · intro a ha; simp [p62] at ha; subst a; trivial
  · exact checked62
theorem derived62 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c62 := by
  apply localUnsat_implies_entails f62 [c60, c58, c45, c32] c62 unsat62 (by rfl) a
  have h0 : Entails.eval a c60 := derived60 a h
  have h1 : Entails.eval a c58 := derived58 a h
  have h2 : Entails.eval a c45 := derived45 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c63 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f63 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c62, some c61, some c28]
def p63 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked63 : lratChecker f63 p63 = .success := by decide +kernel
theorem unsat63 : Unsatisfiable (PosFin 29) f63 := by
  apply lratCheckerSound f63 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p63
  · intro a ha; simp [p63] at ha; subst a; trivial
  · exact checked63
theorem derived63 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c63 := by
  apply localUnsat_implies_entails f63 [c62, c61, c28] c63 unsat63 (by rfl) a
  have h0 : Entails.eval a c62 := derived62 a h
  have h1 : Entails.eval a c61 := derived61 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived63

end CochromaticTwenty.Certificates.Z12Direct_4_3_5
