import MerLeanExperiment.Certificates.Z12Direct_5_0_2.Inputs

/-! Generated from the actual pinned z12direct_5_0_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_0_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c64 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f64 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c10, some c26, some c24, some c48, some c57, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p64 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked64 : lratChecker f64 p64 = .success := by decide +kernel
theorem unsat64 : Unsatisfiable (PosFin 31) f64 := by
  apply lratCheckerSound f64 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p64
  · intro a ha; simp [p64] at ha; subst a; trivial
  · exact checked64
theorem derived64 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c64 := by
  apply localUnsat_implies_entails f64 [c10, c26, c24, c48, c57] c64 unsat64 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c65 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f65 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c23, some c58, some c61, some c60, some c35, some c37, some c64, some c8, some c47, some c27, some c41, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p65 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked65 : lratChecker f65 p65 = .success := by decide +kernel
theorem unsat65 : Unsatisfiable (PosFin 31) f65 := by
  apply lratCheckerSound f65 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p65
  · intro a ha; simp [p65] at ha; subst a; trivial
  · exact checked65
theorem derived65 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c65 := by
  apply localUnsat_implies_entails f65 [c23, c58, c61, c60, c35, c37, c64, c8, c47, c27, c41] c65 unsat65 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c64 := derived64 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c66 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f66 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c23, some c58, some c61, some c29, some c31, some c65, some c25, some c5, some c7, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p66 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked66 : lratChecker f66 p66 = .success := by decide +kernel
theorem unsat66 : Unsatisfiable (PosFin 31) f66 := by
  apply lratCheckerSound f66 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p66
  · intro a ha; simp [p66] at ha; subst a; trivial
  · exact checked66
theorem derived66 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c66 := by
  apply localUnsat_implies_entails f66 [c23, c58, c61, c29, c31, c65, c25, c5, c7] c66 unsat66 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c65 := derived65 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c67 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨22, by decide⟩, true), (⟨20, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f67 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c58, some c3, some c2, some c1, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p67 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked67 : lratChecker f67 p67 = .success := by decide +kernel
theorem unsat67 : Unsatisfiable (PosFin 31) f67 := by
  apply lratCheckerSound f67 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p67
  · intro a ha; simp [p67] at ha; subst a; trivial
  · exact checked67
theorem derived67 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c67 := by
  apply localUnsat_implies_entails f67 [c58, c3, c2, c1] c67 unsat67 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c68 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f68 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c66, some c53, some c55, some c29, some c35, some c58, some c32, some c38, some c67, some c28, some c6, some c8, some c4, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p68 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked68 : lratChecker f68 p68 = .success := by decide +kernel
theorem unsat68 : Unsatisfiable (PosFin 31) f68 := by
  apply lratCheckerSound f68 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p68
  · intro a ha; simp [p68] at ha; subst a; trivial
  · exact checked68
theorem derived68 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c68 := by
  apply localUnsat_implies_entails f68 [c66, c53, c55, c29, c35, c58, c32, c38, c67, c28, c6, c8, c4] c68 unsat68 (by rfl) a
  have h0 : Entails.eval a c66 := derived66 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c67 := derived67 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c69 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f69 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c68, some c62, some c23, some c38, some c55, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p69 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked69 : lratChecker f69 p69 = .success := by decide +kernel
theorem unsat69 : Unsatisfiable (PosFin 31) f69 := by
  apply lratCheckerSound f69 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p69
  · intro a ha; simp [p69] at ha; subst a; trivial
  · exact checked69
theorem derived69 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c69 := by
  apply localUnsat_implies_entails f69 [c68, c62, c23, c38, c55] c69 unsat69 (by rfl) a
  have h0 : Entails.eval a c68 := derived68 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c70 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f70 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c62, some c59, some c53, some c55, some c11, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p70 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked70 : lratChecker f70 p70 = .success := by decide +kernel
theorem unsat70 : Unsatisfiable (PosFin 31) f70 := by
  apply lratCheckerSound f70 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p70
  · intro a ha; simp [p70] at ha; subst a; trivial
  · exact checked70
theorem derived70 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c70 := by
  apply localUnsat_implies_entails f70 [c62, c59, c53, c55, c11] c70 unsat70 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c71 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f71 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c61, some c13, some c15, some c51, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p71 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked71 : lratChecker f71 p71 = .success := by decide +kernel
theorem unsat71 : Unsatisfiable (PosFin 31) f71 := by
  apply lratCheckerSound f71 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p71
  · intro a ha; simp [p71] at ha; subst a; trivial
  · exact checked71
theorem derived71 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c71 := by
  apply localUnsat_implies_entails f71 [c61, c13, c15, c51] c71 unsat71 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c72 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f72 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c68, some c69, some c58, some c61, some c70, some c71, some c39, some c45, some c9, some c51, some c33, some c10, some c17, some c49, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p72 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked72 : lratChecker f72 p72 = .success := by decide +kernel
theorem unsat72 : Unsatisfiable (PosFin 31) f72 := by
  apply lratCheckerSound f72 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p72
  · intro a ha; simp [p72] at ha; subst a; trivial
  · exact checked72
theorem derived72 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c72 := by
  apply localUnsat_implies_entails f72 [c68, c69, c58, c61, c70, c71, c39, c45, c9, c51, c33, c10, c17, c49] c72 unsat72 (by rfl) a
  have h0 : Entails.eval a c68 := derived68 a h
  have h1 : Entails.eval a c69 := derived69 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c70 := derived70 a h
  have h5 : Entails.eval a c71 := derived71 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c73 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f73 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c54, some c58, some c61, some c9, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p73 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked73 : lratChecker f73 p73 = .success := by decide +kernel
theorem unsat73 : Unsatisfiable (PosFin 31) f73 := by
  apply lratCheckerSound f73 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p73
  · intro a ha; simp [p73] at ha; subst a; trivial
  · exact checked73
theorem derived73 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c73 := by
  apply localUnsat_implies_entails f73 [c56, c54, c58, c61, c9] c73 unsat73 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c74 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f74 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c72, some c73, some c23, some c55, some c56, some c14, some c15, some c46, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p74 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked74 : lratChecker f74 p74 = .success := by decide +kernel
theorem unsat74 : Unsatisfiable (PosFin 31) f74 := by
  apply lratCheckerSound f74 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p74
  · intro a ha; simp [p74] at ha; subst a; trivial
  · exact checked74
theorem derived74 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c74 := by
  apply localUnsat_implies_entails f74 [c72, c73, c23, c55, c56, c14, c15, c46] c74 unsat74 (by rfl) a
  have h0 : Entails.eval a c72 := derived72 a h
  have h1 : Entails.eval a c73 := derived73 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c75 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f75 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c72, some c54, some c56, some c73, some c23, some c53, some c74, some c36, some c12, some c30, some c18, some c19, some c43, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p75 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked75 : lratChecker f75 p75 = .success := by decide +kernel
theorem unsat75 : Unsatisfiable (PosFin 31) f75 := by
  apply lratCheckerSound f75 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p75
  · intro a ha; simp [p75] at ha; subst a; trivial
  · exact checked75
theorem derived75 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c75 := by
  apply localUnsat_implies_entails f75 [c72, c54, c56, c73, c23, c53, c74, c36, c12, c30, c18, c19, c43] c75 unsat75 (by rfl) a
  have h0 : Entails.eval a c72 := derived72 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c73 := derived73 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c74 := derived74 a h
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c76 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f76 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c73, some c56, some c54, some c53, some c55, some c36, some c42, some c12, some c63, some c16, some c30, some c19, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p76 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked76 : lratChecker f76 p76 = .success := by decide +kernel
theorem unsat76 : Unsatisfiable (PosFin 31) f76 := by
  apply lratCheckerSound f76 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p76
  · intro a ha; simp [p76] at ha; subst a; trivial
  · exact checked76
theorem derived76 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c76 := by
  apply localUnsat_implies_entails f76 [c75, c73, c56, c54, c53, c55, c36, c42, c12, c63, c16, c30, c19] c76 unsat76 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c73 := derived73 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c77 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f77 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c73, some c56, some c76, some c20, some c40, some c52, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p77 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked77 : lratChecker f77 p77 = .success := by decide +kernel
theorem unsat77 : Unsatisfiable (PosFin 31) f77 := by
  apply lratCheckerSound f77 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p77
  · intro a ha; simp [p77] at ha; subst a; trivial
  · exact checked77
theorem derived77 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c77 := by
  apply localUnsat_implies_entails f77 [c75, c73, c56, c76, c20, c40, c52] c77 unsat77 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c73 := derived73 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c76 := derived76 a h
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c78 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f78 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c54, some c56, some c77, some c9, some c73, some c34, some c20, some c50, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p78 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked78 : lratChecker f78 p78 = .success := by decide +kernel
theorem unsat78 : Unsatisfiable (PosFin 31) f78 := by
  apply lratCheckerSound f78 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p78
  · intro a ha; simp [p78] at ha; subst a; trivial
  · exact checked78
theorem derived78 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c78 := by
  apply localUnsat_implies_entails f78 [c75, c54, c56, c77, c9, c73, c34, c20, c50] c78 unsat78 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c77 := derived77 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c73 := derived73 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c79 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f79 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c56, some c77, some c14, some c78, some c55, some c46, some c15, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p79 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked79 : lratChecker f79 p79 = .success := by decide +kernel
theorem unsat79 : Unsatisfiable (PosFin 31) f79 := by
  apply lratCheckerSound f79 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p79
  · intro a ha; simp [p79] at ha; subst a; trivial
  · exact checked79
theorem derived79 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c79 := by
  apply localUnsat_implies_entails f79 [c56, c77, c14, c78, c55, c46, c15] c79 unsat79 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c77 := derived77 a h
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c78 := derived78 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c80 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f80 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c79, some c53, some c55, some c70, some c35, some c22, some c29, some c61, some c50, some c32, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p80 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked80 : lratChecker f80 p80 = .success := by decide +kernel
theorem unsat80 : Unsatisfiable (PosFin 31) f80 := by
  apply lratCheckerSound f80 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p80
  · intro a ha; simp [p80] at ha; subst a; trivial
  · exact checked80
theorem derived80 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c80 := by
  apply localUnsat_implies_entails f80 [c75, c79, c53, c55, c70, c35, c22, c29, c61, c50, c32] c80 unsat80 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c79 := derived79 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c70 := derived70 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c81 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f81 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c80, some c75, some c21, some c32, some c34, some c44, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p81 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked81 : lratChecker f81 p81 = .success := by decide +kernel
theorem unsat81 : Unsatisfiable (PosFin 31) f81 := by
  apply lratCheckerSound f81 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p81
  · intro a ha; simp [p81] at ha; subst a; trivial
  · exact checked81
theorem derived81 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c81 := by
  apply localUnsat_implies_entails f81 [c79, c80, c75, c21, c32, c34, c44] c81 unsat81 (by rfl) a
  have h0 : Entails.eval a c79 := derived79 a h
  have h1 : Entails.eval a c80 := derived80 a h
  have h2 : Entails.eval a c75 := derived75 a h
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c82 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f82 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c79, some c80, some c50, some c59, some c31, some c29, some c44, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p82 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked82 : lratChecker f82 p82 = .success := by decide +kernel
theorem unsat82 : Unsatisfiable (PosFin 31) f82 := by
  apply lratCheckerSound f82 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p82
  · intro a ha; simp [p82] at ha; subst a; trivial
  · exact checked82
theorem derived82 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c82 := by
  apply localUnsat_implies_entails f82 [c75, c79, c80, c50, c59, c31, c29, c44] c82 unsat82 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c79 := derived79 a h
  have h2 : Entails.eval a c80 := derived80 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c83 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f83 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c21, some c81, some c82, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p83 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked83 : lratChecker f83 p83 = .success := by decide +kernel
theorem unsat83 : Unsatisfiable (PosFin 31) f83 := by
  apply lratCheckerSound f83 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p83
  · intro a ha; simp [p83] at ha; subst a; trivial
  · exact checked83
theorem derived83 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c83 := by
  apply localUnsat_implies_entails f83 [c79, c21, c81, c82] c83 unsat83 (by rfl) a
  have h0 : Entails.eval a c79 := derived79 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c81 := derived81 a h
  have h3 : Entails.eval a c82 := derived82 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c84 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f84 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c58, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p84 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked84 : lratChecker f84 p84 = .success := by decide +kernel
theorem unsat84 : Unsatisfiable (PosFin 31) f84 := by
  apply lratCheckerSound f84 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p84
  · intro a ha; simp [p84] at ha; subst a; trivial
  · exact checked84
theorem derived84 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c84 := by
  apply localUnsat_implies_entails f84 [c83, c58] c84 unsat84 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c85 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f85 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c61, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p85 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked85 : lratChecker f85 p85 = .success := by decide +kernel
theorem unsat85 : Unsatisfiable (PosFin 31) f85 := by
  apply lratCheckerSound f85 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p85
  · intro a ha; simp [p85] at ha; subst a; trivial
  · exact checked85
theorem derived85 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c85 := by
  apply localUnsat_implies_entails f85 [c83, c61] c85 unsat85 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c86 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f86 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c84, some c83, some c29, some c17, some c19, some c49, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p86 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked86 : lratChecker f86 p86 = .success := by decide +kernel
theorem unsat86 : Unsatisfiable (PosFin 31) f86 := by
  apply lratCheckerSound f86 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p86
  · intro a ha; simp [p86] at ha; subst a; trivial
  · exact checked86
theorem derived86 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c86 := by
  apply localUnsat_implies_entails f86 [c79, c84, c83, c29, c17, c19, c49] c86 unsat86 (by rfl) a
  have h0 : Entails.eval a c79 := derived79 a h
  have h1 : Entails.eval a c84 := derived84 a h
  have h2 : Entails.eval a c83 := derived83 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c87 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f87 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c80, some c85, some c84, some c83, some c31, some c9, some c71, some c39, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p87 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked87 : lratChecker f87 p87 = .success := by decide +kernel
theorem unsat87 : Unsatisfiable (PosFin 31) f87 := by
  apply lratCheckerSound f87 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p87
  · intro a ha; simp [p87] at ha; subst a; trivial
  · exact checked87
theorem derived87 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c87 := by
  apply localUnsat_implies_entails f87 [c80, c85, c84, c83, c31, c9, c71, c39] c87 unsat87 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c85 := derived85 a h
  have h2 : Entails.eval a c84 := derived84 a h
  have h3 : Entails.eval a c83 := derived83 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c71 := derived71 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c88 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f88 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c86, some c83, some c87, some c33, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p88 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked88 : lratChecker f88 p88 = .success := by decide +kernel
theorem unsat88 : Unsatisfiable (PosFin 31) f88 := by
  apply lratCheckerSound f88 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p88
  · intro a ha; simp [p88] at ha; subst a; trivial
  · exact checked88
theorem derived88 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c88 := by
  apply localUnsat_implies_entails f88 [c86, c83, c87, c33] c88 unsat88 (by rfl) a
  have h0 : Entails.eval a c86 := derived86 a h
  have h1 : Entails.eval a c83 := derived83 a h
  have h2 : Entails.eval a c87 := derived87 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c89 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f89 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c87, some c86, some c75, some c44, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p89 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked89 : lratChecker f89 p89 = .success := by decide +kernel
theorem unsat89 : Unsatisfiable (PosFin 31) f89 := by
  apply lratCheckerSound f89 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p89
  · intro a ha; simp [p89] at ha; subst a; trivial
  · exact checked89
theorem derived89 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c89 := by
  apply localUnsat_implies_entails f89 [c87, c86, c75, c44] c89 unsat89 (by rfl) a
  have h0 : Entails.eval a c87 := derived87 a h
  have h1 : Entails.eval a c86 := derived86 a h
  have h2 : Entails.eval a c75 := derived75 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c90 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f90 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c89, some c88, some c79, some c22]
def p90 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked90 : lratChecker f90 p90 = .success := by decide +kernel
theorem unsat90 : Unsatisfiable (PosFin 31) f90 := by
  apply lratCheckerSound f90 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p90
  · intro a ha; simp [p90] at ha; subst a; trivial
  · exact checked90
theorem derived90 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c90 := by
  apply localUnsat_implies_entails f90 [c89, c88, c79, c22] c90 unsat90 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c88 := derived88 a h
  have h2 : Entails.eval a c79 := derived79 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived90

end CochromaticTwenty.Certificates.Z12Direct_5_0_2
