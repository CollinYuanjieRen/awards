import MerLeanExperiment.Certificates.Z12Direct_4_3_1.Inputs

/-! Generated from the actual pinned z12direct_4_3_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c71 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f71 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c20, some c41, some c30, some c16, some c19, some c58, some c40, some c7, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p71 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked71 : lratChecker f71 p71 = .success := by decide +kernel
theorem unsat71 : Unsatisfiable (PosFin 29) f71 := by
  apply lratCheckerSound f71 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p71
  · intro a ha; simp [p71] at ha; subst a; trivial
  · exact checked71
theorem derived71 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c71 := by
  apply localUnsat_implies_entails f71 [c20, c41, c30, c16, c19, c58, c40, c7] c71 unsat71 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c72 : DefaultClause 29 := directClause [(⟨2, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f72 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c41, some c30, some c38, some c68, some c17, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p72 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked72 : lratChecker f72 p72 = .success := by decide +kernel
theorem unsat72 : Unsatisfiable (PosFin 29) f72 := by
  apply lratCheckerSound f72 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p72
  · intro a ha; simp [p72] at ha; subst a; trivial
  · exact checked72
theorem derived72 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c72 := by
  apply localUnsat_implies_entails f72 [c41, c30, c38, c68, c17] c72 unsat72 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c73 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f73 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c20, some c41, some c30, some c71, some c72, some c6, some c58, some c15, some c26, some c45, some c43, some c55, some c60, some c64, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p73 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked73 : lratChecker f73 p73 = .success := by decide +kernel
theorem unsat73 : Unsatisfiable (PosFin 29) f73 := by
  apply lratCheckerSound f73 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p73
  · intro a ha; simp [p73] at ha; subst a; trivial
  · exact checked73
theorem derived73 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c73 := by
  apply localUnsat_implies_entails f73 [c20, c41, c30, c71, c72, c6, c58, c15, c26, c45, c43, c55, c60, c64] c73 unsat73 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c71 := derived71 a h
  have h4 : Entails.eval a c72 := derived72 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c74 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨9, by decide⟩, false), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f74 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c41, some c72, some c6, some c58, some c45, some c21, some c49, some c43, some c56, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p74 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked74 : lratChecker f74 p74 = .success := by decide +kernel
theorem unsat74 : Unsatisfiable (PosFin 29) f74 := by
  apply lratCheckerSound f74 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p74
  · intro a ha; simp [p74] at ha; subst a; trivial
  · exact checked74
theorem derived74 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c74 := by
  apply localUnsat_implies_entails f74 [c73, c41, c72, c6, c58, c45, c21, c49, c43, c56] c74 unsat74 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c72 := derived72 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c75 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f75 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c72, some c41, some c26, some c46, some c19, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p75 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked75 : lratChecker f75 p75 = .success := by decide +kernel
theorem unsat75 : Unsatisfiable (PosFin 29) f75 := by
  apply lratCheckerSound f75 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p75
  · intro a ha; simp [p75] at ha; subst a; trivial
  · exact checked75
theorem derived75 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c75 := by
  apply localUnsat_implies_entails f75 [c72, c41, c26, c46, c19] c75 unsat75 (by rfl) a
  have h0 : Entails.eval a c72 := derived72 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c76 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f76 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c41, some c72, some c6, some c58, some c28, some c45, some c74, some c9, some c43, some c34, some c63, some c31, some c57, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p76 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked76 : lratChecker f76 p76 = .success := by decide +kernel
theorem unsat76 : Unsatisfiable (PosFin 29) f76 := by
  apply lratCheckerSound f76 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p76
  · intro a ha; simp [p76] at ha; subst a; trivial
  · exact checked76
theorem derived76 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c76 := by
  apply localUnsat_implies_entails f76 [c73, c41, c72, c6, c58, c28, c45, c74, c9, c43, c34, c63, c31, c57] c76 unsat76 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c72 := derived72 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c74 := derived74 a h
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c77 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f77 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c41, some c72, some c6, some c58, some c76, some c10, some c46, some c75, some c34, some c19, some c14, some c33, some c55, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p77 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked77 : lratChecker f77 p77 = .success := by decide +kernel
theorem unsat77 : Unsatisfiable (PosFin 29) f77 := by
  apply lratCheckerSound f77 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p77
  · intro a ha; simp [p77] at ha; subst a; trivial
  · exact checked77
theorem derived77 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c77 := by
  apply localUnsat_implies_entails f77 [c41, c72, c6, c58, c76, c10, c46, c75, c34, c19, c14, c33, c55] c77 unsat77 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c72 := derived72 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c76 := derived76 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c75 := derived75 a h
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c78 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f78 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c6, some c46, some c12, some c44, some c1, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p78 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked78 : lratChecker f78 p78 = .success := by decide +kernel
theorem unsat78 : Unsatisfiable (PosFin 29) f78 := by
  apply lratCheckerSound f78 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p78
  · intro a ha; simp [p78] at ha; subst a; trivial
  · exact checked78
theorem derived78 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c78 := by
  apply localUnsat_implies_entails f78 [c6, c46, c12, c44, c1] c78 unsat78 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c79 : DefaultClause 29 := directClause [(⟨5, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f79 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c38, some c28, some c63, some c65, some c27, some c24, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p79 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked79 : lratChecker f79 p79 = .success := by decide +kernel
theorem unsat79 : Unsatisfiable (PosFin 29) f79 := by
  apply lratCheckerSound f79 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p79
  · intro a ha; simp [p79] at ha; subst a; trivial
  · exact checked79
theorem derived79 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c79 := by
  apply localUnsat_implies_entails f79 [c73, c38, c28, c63, c65, c27, c24] c79 unsat79 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c80 : DefaultClause 29 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f80 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c77, some c17, some c38, some c6, some c78, some c45, some c79, some c8, some c33, some c32, some c44, some c34, some c67, some c53, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p80 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked80 : lratChecker f80 p80 = .success := by decide +kernel
theorem unsat80 : Unsatisfiable (PosFin 29) f80 := by
  apply lratCheckerSound f80 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p80
  · intro a ha; simp [p80] at ha; subst a; trivial
  · exact checked80
theorem derived80 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c80 := by
  apply localUnsat_implies_entails f80 [c77, c17, c38, c6, c78, c45, c79, c8, c33, c32, c44, c34, c67, c53] c80 unsat80 (by rfl) a
  have h0 : Entails.eval a c77 := derived77 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c78 := derived78 a h
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c79 := derived79 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c81 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f81 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c77, some c78, some c45, some c8, some c33, some c44, some c2, some c34, some c29, some c35, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p81 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked81 : lratChecker f81 p81 = .success := by decide +kernel
theorem unsat81 : Unsatisfiable (PosFin 29) f81 := by
  apply lratCheckerSound f81 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p81
  · intro a ha; simp [p81] at ha; subst a; trivial
  · exact checked81
theorem derived81 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c81 := by
  apply localUnsat_implies_entails f81 [c77, c78, c45, c8, c33, c44, c2, c34, c29, c35] c81 unsat81 (by rfl) a
  have h0 : Entails.eval a c77 := derived77 a h
  have h1 : Entails.eval a c78 := derived78 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c82 : DefaultClause 29 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f82 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c77, some c6, some c78, some c45, some c81, some c79, some c49, some c48, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p82 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked82 : lratChecker f82 p82 = .success := by decide +kernel
theorem unsat82 : Unsatisfiable (PosFin 29) f82 := by
  apply lratCheckerSound f82 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p82
  · intro a ha; simp [p82] at ha; subst a; trivial
  · exact checked82
theorem derived82 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c82 := by
  apply localUnsat_implies_entails f82 [c77, c6, c78, c45, c81, c79, c49, c48] c82 unsat82 (by rfl) a
  have h0 : Entails.eval a c77 := derived77 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c78 := derived78 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c81 := derived81 a h
  have h5 : Entails.eval a c79 := derived79 a h
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c83 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f83 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c77, some c82, some c38, some c11, some c80, some c29, some c49, some c70, some c61, some c62, some c51, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p83 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked83 : lratChecker f83 p83 = .success := by decide +kernel
theorem unsat83 : Unsatisfiable (PosFin 29) f83 := by
  apply lratCheckerSound f83 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p83
  · intro a ha; simp [p83] at ha; subst a; trivial
  · exact checked83
theorem derived83 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c83 := by
  apply localUnsat_implies_entails f83 [c77, c82, c38, c11, c80, c29, c49, c70, c61, c62, c51] c83 unsat83 (by rfl) a
  have h0 : Entails.eval a c77 := derived77 a h
  have h1 : Entails.eval a c82 := derived82 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c80 := derived80 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c84 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f84 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c4, some c40, some c19, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p84 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked84 : lratChecker f84 p84 = .success := by decide +kernel
theorem unsat84 : Unsatisfiable (PosFin 29) f84 := by
  apply lratCheckerSound f84 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p84
  · intro a ha; simp [p84] at ha; subst a; trivial
  · exact checked84
theorem derived84 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c84 := by
  apply localUnsat_implies_entails f84 [c4, c40, c19] c84 unsat84 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c85 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f85 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c80, some c82, some c83, some c84, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p85 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked85 : lratChecker f85 p85 = .success := by decide +kernel
theorem unsat85 : Unsatisfiable (PosFin 29) f85 := by
  apply lratCheckerSound f85 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p85
  · intro a ha; simp [p85] at ha; subst a; trivial
  · exact checked85
theorem derived85 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c85 := by
  apply localUnsat_implies_entails f85 [c80, c82, c83, c84] c85 unsat85 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c82 := derived82 a h
  have h2 : Entails.eval a c83 := derived83 a h
  have h3 : Entails.eval a c84 := derived84 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c86 : DefaultClause 29 := directClause [(⟨2, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f86 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c85, some c77, some c38, some c17, some c11, some c84, some c29, some c42, some c70, some c19, some c23, some c22, some c27, some c5, some c66, some c50, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p86 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked86 : lratChecker f86 p86 = .success := by decide +kernel
theorem unsat86 : Unsatisfiable (PosFin 29) f86 := by
  apply lratCheckerSound f86 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p86
  · intro a ha; simp [p86] at ha; subst a; trivial
  · exact checked86
theorem derived86 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c86 := by
  apply localUnsat_implies_entails f86 [c73, c85, c77, c38, c17, c11, c84, c29, c42, c70, c19, c23, c22, c27, c5, c66, c50] c86 unsat86 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c85 := derived85 a h
  have h2 : Entails.eval a c77 := derived77 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c84 := derived84 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c5 := h 4 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c87 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f87 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c85, some c77, some c86, some c28, some c69, some c11, some c59, some c8, some c33, some c44, some c47, some c54, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p87 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked87 : lratChecker f87 p87 = .success := by decide +kernel
theorem unsat87 : Unsatisfiable (PosFin 29) f87 := by
  apply lratCheckerSound f87 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p87
  · intro a ha; simp [p87] at ha; subst a; trivial
  · exact checked87
theorem derived87 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c87 := by
  apply localUnsat_implies_entails f87 [c73, c85, c77, c86, c28, c69, c11, c59, c8, c33, c44, c47, c54] c87 unsat87 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c85 := derived85 a h
  have h2 : Entails.eval a c77 := derived77 a h
  have h3 : Entails.eval a c86 := derived86 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c88 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f88 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c73, some c77, some c85, some c86, some c28, some c69, some c87, some c37, some c48, some c29, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p88 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked88 : lratChecker f88 p88 = .success := by decide +kernel
theorem unsat88 : Unsatisfiable (PosFin 29) f88 := by
  apply lratCheckerSound f88 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p88
  · intro a ha; simp [p88] at ha; subst a; trivial
  · exact checked88
theorem derived88 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c88 := by
  apply localUnsat_implies_entails f88 [c73, c77, c85, c86, c28, c69, c87, c37, c48, c29] c88 unsat88 (by rfl) a
  have h0 : Entails.eval a c73 := derived73 a h
  have h1 : Entails.eval a c77 := derived77 a h
  have h2 : Entails.eval a c85 := derived85 a h
  have h3 : Entails.eval a c86 := derived86 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c87 := derived87 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c89 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f89 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c88, some c30, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p89 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked89 : lratChecker f89 p89 = .success := by decide +kernel
theorem unsat89 : Unsatisfiable (PosFin 29) f89 := by
  apply lratCheckerSound f89 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p89
  · intro a ha; simp [p89] at ha; subst a; trivial
  · exact checked89
theorem derived89 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c89 := by
  apply localUnsat_implies_entails f89 [c88, c30] c89 unsat89 (by rfl) a
  have h0 : Entails.eval a c88 := derived88 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c90 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f90 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c89, some c41, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p90 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked90 : lratChecker f90 p90 = .success := by decide +kernel
theorem unsat90 : Unsatisfiable (PosFin 29) f90 := by
  apply lratCheckerSound f90 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p90
  · intro a ha; simp [p90] at ha; subst a; trivial
  · exact checked90
theorem derived90 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c90 := by
  apply localUnsat_implies_entails f90 [c89, c41] c90 unsat90 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c91 : DefaultClause 29 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f91 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c88, some c90, some c73, some c89, some c28, some c69, some c17, some c11, some c59, some c13, some c37, some c8, some c44, some c5, some c47, some c52, some c25, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p91 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked91 : lratChecker f91 p91 = .success := by decide +kernel
theorem unsat91 : Unsatisfiable (PosFin 29) f91 := by
  apply lratCheckerSound f91 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p91
  · intro a ha; simp [p91] at ha; subst a; trivial
  · exact checked91
theorem derived91 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c91 := by
  apply localUnsat_implies_entails f91 [c88, c90, c73, c89, c28, c69, c17, c11, c59, c13, c37, c8, c44, c5, c47, c52, c25] c91 unsat91 (by rfl) a
  have h0 : Entails.eval a c88 := derived88 a h
  have h1 : Entails.eval a c90 := derived90 a h
  have h2 : Entails.eval a c73 := derived73 a h
  have h3 : Entails.eval a c89 := derived89 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c52 := h 51 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c92 : DefaultClause 29 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f92 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c91, some c38, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p92 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked92 : lratChecker f92 p92 = .success := by decide +kernel
theorem unsat92 : Unsatisfiable (PosFin 29) f92 := by
  apply lratCheckerSound f92 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p92
  · intro a ha; simp [p92] at ha; subst a; trivial
  · exact checked92
theorem derived92 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c92 := by
  apply localUnsat_implies_entails f92 [c91, c38] c92 unsat92 (by rfl) a
  have h0 : Entails.eval a c91 := derived91 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c93 : DefaultClause 29 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f93 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c92, some c17, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p93 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked93 : lratChecker f93 p93 = .success := by decide +kernel
theorem unsat93 : Unsatisfiable (PosFin 29) f93 := by
  apply lratCheckerSound f93 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p93
  · intro a ha; simp [p93] at ha; subst a; trivial
  · exact checked93
theorem derived93 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c93 := by
  apply localUnsat_implies_entails f93 [c92, c17] c93 unsat93 (by rfl) a
  have h0 : Entails.eval a c92 := derived92 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c94 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f94 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c92, some c90, some c11, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p94 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked94 : lratChecker f94 p94 = .success := by decide +kernel
theorem unsat94 : Unsatisfiable (PosFin 29) f94 := by
  apply lratCheckerSound f94 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p94
  · intro a ha; simp [p94] at ha; subst a; trivial
  · exact checked94
theorem derived94 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c94 := by
  apply localUnsat_implies_entails f94 [c92, c90, c11] c94 unsat94 (by rfl) a
  have h0 : Entails.eval a c92 := derived92 a h
  have h1 : Entails.eval a c90 := derived90 a h
  have h2 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c95 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f95 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c93, some c91, some c84, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p95 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked95 : lratChecker f95 p95 = .success := by decide +kernel
theorem unsat95 : Unsatisfiable (PosFin 29) f95 := by
  apply lratCheckerSound f95 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p95
  · intro a ha; simp [p95] at ha; subst a; trivial
  · exact checked95
theorem derived95 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c95 := by
  apply localUnsat_implies_entails f95 [c93, c91, c84] c95 unsat95 (by rfl) a
  have h0 : Entails.eval a c93 := derived93 a h
  have h1 : Entails.eval a c91 := derived91 a h
  have h2 : Entails.eval a c84 := derived84 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c96 : DefaultClause 29 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f96 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c94, some c89, some c73, some c59, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p96 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked96 : lratChecker f96 p96 = .success := by decide +kernel
theorem unsat96 : Unsatisfiable (PosFin 29) f96 := by
  apply lratCheckerSound f96 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p96
  · intro a ha; simp [p96] at ha; subst a; trivial
  · exact checked96
theorem derived96 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c96 := by
  apply localUnsat_implies_entails f96 [c94, c89, c73, c59] c96 unsat96 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c89 := derived89 a h
  have h2 : Entails.eval a c73 := derived73 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c97 : DefaultClause 29 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c95, some c96, some c88, some c36, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p97 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 29) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c95, c96, c88, c36] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c95 := derived95 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c88 := derived88 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c98 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c93, some c91, some c3, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p98 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 29) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c97, c93, c91, c3] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c93 := derived93 a h
  have h2 : Entails.eval a c91 := derived91 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c99 : DefaultClause 29 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c97, some c39, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p99 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 29) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c97, c39] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c97 := derived97 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c100 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c99, some c98, some c18]
def p100 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 29) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c99, c98, c18] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c99 := derived99 a h
  have h1 : Entails.eval a c98 := derived98 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived100

end CochromaticTwenty.Certificates.Z12Direct_4_3_1
