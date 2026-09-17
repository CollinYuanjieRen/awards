import MerLeanExperiment.Certificates.Z12Direct_4_2_7.Inputs

/-! Generated from the actual pinned z12direct_4_2_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c75 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f75 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c39, some c12, some c3, some c57, some c31, some c16, some c38, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p75 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked75 : lratChecker f75 p75 = .success := by decide +kernel
theorem unsat75 : Unsatisfiable (PosFin 29) f75 := by
  apply lratCheckerSound f75 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p75
  · intro a ha; simp [p75] at ha; subst a; trivial
  · exact checked75
theorem derived75 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c75 := by
  apply localUnsat_implies_entails f75 [c39, c12, c3, c57, c31, c16, c38] c75 unsat75 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c76 : DefaultClause 29 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f76 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c12, some c39, some c75, some c27, some c10, some c57, some c30, some c48, some c38, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p76 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked76 : lratChecker f76 p76 = .success := by decide +kernel
theorem unsat76 : Unsatisfiable (PosFin 29) f76 := by
  apply lratCheckerSound f76 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p76
  · intro a ha; simp [p76] at ha; subst a; trivial
  · exact checked76
theorem derived76 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c76 := by
  apply localUnsat_implies_entails f76 [c12, c39, c75, c27, c10, c57, c30, c48, c38] c76 unsat76 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c75 := derived75 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c77 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f77 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c76, some c7, some c58, some c35, some c36, some c72, some c62, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p77 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked77 : lratChecker f77 p77 = .success := by decide +kernel
theorem unsat77 : Unsatisfiable (PosFin 29) f77 := by
  apply lratCheckerSound f77 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p77
  · intro a ha; simp [p77] at ha; subst a; trivial
  · exact checked77
theorem derived77 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c77 := by
  apply localUnsat_implies_entails f77 [c76, c7, c58, c35, c36, c72, c62] c77 unsat77 (by rfl) a
  have h0 : Entails.eval a c76 := derived76 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c78 : DefaultClause 29 := directClause [(⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f78 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c76, some c7, some c77, some c27, some c55, some c34, some c41, some c25, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p78 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked78 : lratChecker f78 p78 = .success := by decide +kernel
theorem unsat78 : Unsatisfiable (PosFin 29) f78 := by
  apply lratCheckerSound f78 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p78
  · intro a ha; simp [p78] at ha; subst a; trivial
  · exact checked78
theorem derived78 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c78 := by
  apply localUnsat_implies_entails f78 [c76, c7, c77, c27, c55, c34, c41, c25] c78 unsat78 (by rfl) a
  have h0 : Entails.eval a c76 := derived76 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c77 := derived77 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c79 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f79 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c78, some c26, some c76, some c7, some c10, some c55, some c30, some c33, some c64, some c73, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p79 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked79 : lratChecker f79 p79 = .success := by decide +kernel
theorem unsat79 : Unsatisfiable (PosFin 29) f79 := by
  apply lratCheckerSound f79 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p79
  · intro a ha; simp [p79] at ha; subst a; trivial
  · exact checked79
theorem derived79 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c79 := by
  apply localUnsat_implies_entails f79 [c78, c26, c76, c7, c10, c55, c30, c33, c64, c73] c79 unsat79 (by rfl) a
  have h0 : Entails.eval a c78 := derived78 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c76 := derived76 a h
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c80 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f80 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c76, some c7, some c78, some c26, some c79, some c27, some c58, some c31, some c16, some c38, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p80 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked80 : lratChecker f80 p80 = .success := by decide +kernel
theorem unsat80 : Unsatisfiable (PosFin 29) f80 := by
  apply lratCheckerSound f80 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p80
  · intro a ha; simp [p80] at ha; subst a; trivial
  · exact checked80
theorem derived80 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c80 := by
  apply localUnsat_implies_entails f80 [c76, c7, c78, c26, c79, c27, c58, c31, c16, c38] c80 unsat80 (by rfl) a
  have h0 : Entails.eval a c76 := derived76 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c78 := derived78 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c79 := derived79 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c81 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f81 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c80, some c40, some c13, some c55, some c58, some c2, some c3, some c29, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p81 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked81 : lratChecker f81 p81 = .success := by decide +kernel
theorem unsat81 : Unsatisfiable (PosFin 29) f81 := by
  apply lratCheckerSound f81 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p81
  · intro a ha; simp [p81] at ha; subst a; trivial
  · exact checked81
theorem derived81 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c81 := by
  apply localUnsat_implies_entails f81 [c80, c40, c13, c55, c58, c2, c3, c29] c81 unsat81 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c82 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f82 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c81, some c80, some c40, some c13, some c25, some c38, some c20, some c49, some c39, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p82 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked82 : lratChecker f82 p82 = .success := by decide +kernel
theorem unsat82 : Unsatisfiable (PosFin 29) f82 := by
  apply lratCheckerSound f82 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p82
  · intro a ha; simp [p82] at ha; subst a; trivial
  · exact checked82
theorem derived82 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c82 := by
  apply localUnsat_implies_entails f82 [c81, c80, c40, c13, c25, c38, c20, c49, c39] c82 unsat82 (by rfl) a
  have h0 : Entails.eval a c81 := derived81 a h
  have h1 : Entails.eval a c80 := derived80 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c83 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f83 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c80, some c13, some c40, some c81, some c82, some c42, some c12, some c39, some c10, some c15, some c19, some c32, some c68, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p83 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked83 : lratChecker f83 p83 = .success := by decide +kernel
theorem unsat83 : Unsatisfiable (PosFin 29) f83 := by
  apply lratCheckerSound f83 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p83
  · intro a ha; simp [p83] at ha; subst a; trivial
  · exact checked83
theorem derived83 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c83 := by
  apply localUnsat_implies_entails f83 [c80, c13, c40, c81, c82, c42, c12, c39, c10, c15, c19, c32, c68] c83 unsat83 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c81 := derived81 a h
  have h4 : Entails.eval a c82 := derived82 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c84 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f84 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c83, some c52, some c2, some c42, some c49, some c50, some c14, some c60, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p84 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked84 : lratChecker f84 p84 = .success := by decide +kernel
theorem unsat84 : Unsatisfiable (PosFin 29) f84 := by
  apply lratCheckerSound f84 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p84
  · intro a ha; simp [p84] at ha; subst a; trivial
  · exact checked84
theorem derived84 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c84 := by
  apply localUnsat_implies_entails f84 [c83, c52, c2, c42, c49, c50, c14, c60] c84 unsat84 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c85 : DefaultClause 29 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨28, by decide⟩, false), (⟨12, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f85 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c84, some c40, some c6, some c7, some c45, some c46, some c28, some c67, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p85 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked85 : lratChecker f85 p85 = .success := by decide +kernel
theorem unsat85 : Unsatisfiable (PosFin 29) f85 := by
  apply lratCheckerSound f85 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p85
  · intro a ha; simp [p85] at ha; subst a; trivial
  · exact checked85
theorem derived85 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c85 := by
  apply localUnsat_implies_entails f85 [c84, c40, c6, c7, c45, c46, c28, c67] c85 unsat85 (by rfl) a
  have h0 : Entails.eval a c84 := derived84 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c86 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f86 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c83, some c52, some c85, some c26, some c10, some c15, some c19, some c30, some c60, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p86 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked86 : lratChecker f86 p86 = .success := by decide +kernel
theorem unsat86 : Unsatisfiable (PosFin 29) f86 := by
  apply lratCheckerSound f86 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p86
  · intro a ha; simp [p86] at ha; subst a; trivial
  · exact checked86
theorem derived86 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c86 := by
  apply localUnsat_implies_entails f86 [c83, c52, c85, c26, c10, c15, c19, c30, c60] c86 unsat86 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c85 := derived85 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c87 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f87 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c86, some c25, some c38, some c20, some c15, some c12, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p87 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked87 : lratChecker f87 p87 = .success := by decide +kernel
theorem unsat87 : Unsatisfiable (PosFin 29) f87 := by
  apply lratCheckerSound f87 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p87
  · intro a ha; simp [p87] at ha; subst a; trivial
  · exact checked87
theorem derived87 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c87 := by
  apply localUnsat_implies_entails f87 [c86, c25, c38, c20, c15, c12] c87 unsat87 (by rfl) a
  have h0 : Entails.eval a c86 := derived86 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c88 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true), (⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f88 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c87, some c83, some c69, some c52, some c25, some c38, some c24, some c9, some c22, some c1, some c63, some c61, some c51, some c47, some c65, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p88 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked88 : lratChecker f88 p88 = .success := by decide +kernel
theorem unsat88 : Unsatisfiable (PosFin 29) f88 := by
  apply lratCheckerSound f88 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p88
  · intro a ha; simp [p88] at ha; subst a; trivial
  · exact checked88
theorem derived88 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c88 := by
  apply localUnsat_implies_entails f88 [c87, c83, c69, c52, c25, c38, c24, c9, c22, c1, c63, c61, c51, c47, c65] c88 unsat88 (by rfl) a
  have h0 : Entails.eval a c87 := derived87 a h
  have h1 : Entails.eval a c83 := derived83 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c89 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false), (⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f89 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c9, some c1, some c30, some c34, some c26, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p89 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked89 : lratChecker f89 p89 = .success := by decide +kernel
theorem unsat89 : Unsatisfiable (PosFin 29) f89 := by
  apply lratCheckerSound f89 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p89
  · intro a ha; simp [p89] at ha; subst a; trivial
  · exact checked89
theorem derived89 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c89 := by
  apply localUnsat_implies_entails f89 [c9, c1, c30, c34, c26] c89 unsat89 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c90 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f90 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c2, some c30, some c40, some c12, some c41, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p90 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked90 : lratChecker f90 p90 = .success := by decide +kernel
theorem unsat90 : Unsatisfiable (PosFin 29) f90 := by
  apply lratCheckerSound f90 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p90
  · intro a ha; simp [p90] at ha; subst a; trivial
  · exact checked90
theorem derived90 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c90 := by
  apply localUnsat_implies_entails f90 [c2, c30, c40, c12, c41] c90 unsat90 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c91 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f91 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c83, some c52, some c87, some c88, some c89, some c90, some c1, some c59, some c10, some c56, some c53, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p91 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked91 : lratChecker f91 p91 = .success := by decide +kernel
theorem unsat91 : Unsatisfiable (PosFin 29) f91 := by
  apply lratCheckerSound f91 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p91
  · intro a ha; simp [p91] at ha; subst a; trivial
  · exact checked91
theorem derived91 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c91 := by
  apply localUnsat_implies_entails f91 [c83, c52, c87, c88, c89, c90, c1, c59, c10, c56, c53] c91 unsat91 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c87 := derived87 a h
  have h3 : Entails.eval a c88 := derived88 a h
  have h4 : Entails.eval a c89 := derived89 a h
  have h5 : Entails.eval a c90 := derived90 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c92 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f92 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c91, some c27, some c83, some c52, some c2, some c44, some c1, some c43, some c31, some c26, some c53, some c54, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p92 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked92 : lratChecker f92 p92 = .success := by decide +kernel
theorem unsat92 : Unsatisfiable (PosFin 29) f92 := by
  apply lratCheckerSound f92 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p92
  · intro a ha; simp [p92] at ha; subst a; trivial
  · exact checked92
theorem derived92 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c92 := by
  apply localUnsat_implies_entails f92 [c91, c27, c83, c52, c2, c44, c1, c43, c31, c26, c53, c54] c92 unsat92 (by rfl) a
  have h0 : Entails.eval a c91 := derived91 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c83 := derived83 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c93 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨1, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f93 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c38, some c25, some c27, some c13, some c16, some c35, some c26, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p93 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked93 : lratChecker f93 p93 = .success := by decide +kernel
theorem unsat93 : Unsatisfiable (PosFin 29) f93 := by
  apply lratCheckerSound f93 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p93
  · intro a ha; simp [p93] at ha; subst a; trivial
  · exact checked93
theorem derived93 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c93 := by
  apply localUnsat_implies_entails f93 [c38, c25, c27, c13, c16, c35, c26] c93 unsat93 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c94 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f94 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c91, some c27, some c13, some c92, some c25, some c38, some c93, some c1, some c17, some c37, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p94 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked94 : lratChecker f94 p94 = .success := by decide +kernel
theorem unsat94 : Unsatisfiable (PosFin 29) f94 := by
  apply lratCheckerSound f94 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p94
  · intro a ha; simp [p94] at ha; subst a; trivial
  · exact checked94
theorem derived94 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c94 := by
  apply localUnsat_implies_entails f94 [c91, c27, c13, c92, c25, c38, c93, c1, c17, c37] c94 unsat94 (by rfl) a
  have h0 : Entails.eval a c91 := derived91 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c92 := derived92 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c93 := derived93 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c95 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f95 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c6, some c11, some c38, some c23, some c45, some c28, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p95 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked95 : lratChecker f95 p95 = .success := by decide +kernel
theorem unsat95 : Unsatisfiable (PosFin 29) f95 := by
  apply lratCheckerSound f95 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p95
  · intro a ha; simp [p95] at ha; subst a; trivial
  · exact checked95
theorem derived95 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c95 := by
  apply localUnsat_implies_entails f95 [c6, c11, c38, c23, c45, c28] c95 unsat95 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c96 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f96 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c91, some c13, some c94, some c95, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p96 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked96 : lratChecker f96 p96 = .success := by decide +kernel
theorem unsat96 : Unsatisfiable (PosFin 29) f96 := by
  apply lratCheckerSound f96 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p96
  · intro a ha; simp [p96] at ha; subst a; trivial
  · exact checked96
theorem derived96 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c96 := by
  apply localUnsat_implies_entails f96 [c91, c13, c94, c95] c96 unsat96 (by rfl) a
  have h0 : Entails.eval a c91 := derived91 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c94 := derived94 a h
  have h3 : Entails.eval a c95 := derived95 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c97 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c96, some c95, some c40, some c13, some c90, some c42, some c12, some c39, some c10, some c15, some c19, some c32, some c11, some c71, some c66, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p97 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 29) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c96, c95, c40, c13, c90, c42, c12, c39, c10, c15, c19, c32, c11, c71, c66] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c95 := derived95 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c90 := derived90 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c98 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c95, some c13, some c40, some c97, some c25, some c38, some c20, some c49, some c39, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p98 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 29) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c95, c13, c40, c97, c25, c38, c20, c49, c39] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c95 := derived95 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c97 := derived97 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c99 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c81, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p99 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 29) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c98, c81] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c81 := derived81 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c100 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c38, some c25, some c13, some c40, some c24, some c9, some c51, some c1, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p100 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 29) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c98, c38, c25, c13, c40, c24, c9, c51, c1] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c101 : DefaultClause 29 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f101 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c100, some c38, some c25, some c1, some c17, some c37, some c8, some c27, some c4, some c24, some c5, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p101 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked101 : lratChecker f101 p101 = .success := by decide +kernel
theorem unsat101 : Unsatisfiable (PosFin 29) f101 := by
  apply lratCheckerSound f101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p101
  · intro a ha; simp [p101] at ha; subst a; trivial
  · exact checked101
theorem derived101 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c101 := by
  apply localUnsat_implies_entails f101 [c98, c100, c38, c25, c1, c17, c37, c8, c27, c4, c24, c5] c101 unsat101 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c100 := derived100 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c102 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f102 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c25, some c101, some c9, some c93, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p102 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked102 : lratChecker f102 p102 = .success := by decide +kernel
theorem unsat102 : Unsatisfiable (PosFin 29) f102 := by
  apply lratCheckerSound f102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p102
  · intro a ha; simp [p102] at ha; subst a; trivial
  · exact checked102
theorem derived102 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c102 := by
  apply localUnsat_implies_entails f102 [c25, c101, c9, c93] c102 unsat102 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c101 := derived101 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c93 := derived93 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c103 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f103 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c102, some c89, some c27, some c2, some c1, some c31, some c35, some c26, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p103 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked103 : lratChecker f103 p103 = .success := by decide +kernel
theorem unsat103 : Unsatisfiable (PosFin 29) f103 := by
  apply lratCheckerSound f103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p103
  · intro a ha; simp [p103] at ha; subst a; trivial
  · exact checked103
theorem derived103 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c103 := by
  apply localUnsat_implies_entails f103 [c98, c102, c89, c27, c2, c1, c31, c35, c26] c103 unsat103 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c102 := derived102 a h
  have h2 : Entails.eval a c89 := derived89 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c104 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f104 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c103, some c11, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p104 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked104 : lratChecker f104 p104 = .success := by decide +kernel
theorem unsat104 : Unsatisfiable (PosFin 29) f104 := by
  apply lratCheckerSound f104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p104
  · intro a ha; simp [p104] at ha; subst a; trivial
  · exact checked104
theorem derived104 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c104 := by
  apply localUnsat_implies_entails f104 [c103, c11] c104 unsat104 (by rfl) a
  have h0 : Entails.eval a c103 := derived103 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c105 : DefaultClause 29 := directClause [(⟨16, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f105 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c98, some c103, some c96, some c99, some c59, some c70, some c74, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p105 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked105 : lratChecker f105 p105 = .success := by decide +kernel
theorem unsat105 : Unsatisfiable (PosFin 29) f105 := by
  apply lratCheckerSound f105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p105
  · intro a ha; simp [p105] at ha; subst a; trivial
  · exact checked105
theorem derived105 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c105 := by
  apply localUnsat_implies_entails f105 [c98, c103, c96, c99, c59, c70, c74] c105 unsat105 (by rfl) a
  have h0 : Entails.eval a c98 := derived98 a h
  have h1 : Entails.eval a c103 := derived103 a h
  have h2 : Entails.eval a c96 := derived96 a h
  have h3 : Entails.eval a c99 := derived99 a h
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c106 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f106 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c102, some c104, some c16, some c12, some c41, some c21, some c105, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p106 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked106 : lratChecker f106 p106 = .success := by decide +kernel
theorem unsat106 : Unsatisfiable (PosFin 29) f106 := by
  apply lratCheckerSound f106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p106
  · intro a ha; simp [p106] at ha; subst a; trivial
  · exact checked106
theorem derived106 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c106 := by
  apply localUnsat_implies_entails f106 [c102, c104, c16, c12, c41, c21, c105] c106 unsat106 (by rfl) a
  have h0 : Entails.eval a c102 := derived102 a h
  have h1 : Entails.eval a c104 := derived104 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c105 := derived105 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c107 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f107 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c102, some c2, some c90, some c27, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p107 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked107 : lratChecker f107 p107 = .success := by decide +kernel
theorem unsat107 : Unsatisfiable (PosFin 29) f107 := by
  apply lratCheckerSound f107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p107
  · intro a ha; simp [p107] at ha; subst a; trivial
  · exact checked107
theorem derived107 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c107 := by
  apply localUnsat_implies_entails f107 [c102, c2, c90, c27] c107 unsat107 (by rfl) a
  have h0 : Entails.eval a c102 := derived102 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c90 := derived90 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c108 : DefaultClause 29 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f108 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c98, some c1, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p108 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked108 : lratChecker f108 p108 = .success := by decide +kernel
theorem unsat108 : Unsatisfiable (PosFin 29) f108 := by
  apply lratCheckerSound f108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p108
  · intro a ha; simp [p108] at ha; subst a; trivial
  · exact checked108
theorem derived108 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c108 := by
  apply localUnsat_implies_entails f108 [c107, c98, c1] c108 unsat108 (by rfl) a
  have h0 : Entails.eval a c107 := derived107 a h
  have h1 : Entails.eval a c98 := derived98 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c109 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f109 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c108, some c106, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p109 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked109 : lratChecker f109 p109 = .success := by decide +kernel
theorem unsat109 : Unsatisfiable (PosFin 29) f109 := by
  apply lratCheckerSound f109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p109
  · intro a ha; simp [p109] at ha; subst a; trivial
  · exact checked109
theorem derived109 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c109 := by
  apply localUnsat_implies_entails f109 [c108, c106] c109 unsat109 (by rfl) a
  have h0 : Entails.eval a c108 := derived108 a h
  have h1 : Entails.eval a c106 := derived106 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c110 : DefaultClause 29 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f110 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c109, some c13, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p110 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked110 : lratChecker f110 p110 = .success := by decide +kernel
theorem unsat110 : Unsatisfiable (PosFin 29) f110 := by
  apply lratCheckerSound f110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p110
  · intro a ha; simp [p110] at ha; subst a; trivial
  · exact checked110
theorem derived110 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c110 := by
  apply localUnsat_implies_entails f110 [c109, c13] c110 unsat110 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c111 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f111 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c109, some c40, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p111 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked111 : lratChecker f111 p111 = .success := by decide +kernel
theorem unsat111 : Unsatisfiable (PosFin 29) f111 := by
  apply lratCheckerSound f111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p111
  · intro a ha; simp [p111] at ha; subst a; trivial
  · exact checked111
theorem derived111 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c111 := by
  apply localUnsat_implies_entails f111 [c109, c40] c111 unsat111 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c112 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f112 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c110, some c108, some c104, some c18, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p112 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked112 : lratChecker f112 p112 = .success := by decide +kernel
theorem unsat112 : Unsatisfiable (PosFin 29) f112 := by
  apply lratCheckerSound f112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p112
  · intro a ha; simp [p112] at ha; subst a; trivial
  · exact checked112
theorem derived112 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c112 := by
  apply localUnsat_implies_entails f112 [c110, c108, c104, c18] c112 unsat112 (by rfl) a
  have h0 : Entails.eval a c110 := derived110 a h
  have h1 : Entails.eval a c108 := derived108 a h
  have h2 : Entails.eval a c104 := derived104 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c113 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f113 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c112, some c111, some c102, some c98, some c44]
def p113 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked113 : lratChecker f113 p113 = .success := by decide +kernel
theorem unsat113 : Unsatisfiable (PosFin 29) f113 := by
  apply lratCheckerSound f113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p113
  · intro a ha; simp [p113] at ha; subst a; trivial
  · exact checked113
theorem derived113 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c113 := by
  apply localUnsat_implies_entails f113 [c112, c111, c102, c98, c44] c113 unsat113 (by rfl) a
  have h0 : Entails.eval a c112 := derived112 a h
  have h1 : Entails.eval a c111 := derived111 a h
  have h2 : Entails.eval a c102 := derived102 a h
  have h3 : Entails.eval a c98 := derived98 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived113

end CochromaticTwenty.Certificates.Z12Direct_4_2_7
