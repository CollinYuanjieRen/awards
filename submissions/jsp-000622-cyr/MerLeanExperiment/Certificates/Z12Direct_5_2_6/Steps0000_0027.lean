import MerLeanExperiment.Certificates.Z12Direct_5_2_6.Inputs

/-! Generated from the actual pinned z12direct_5_2_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_2_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c74 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f74 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c59, some c60, some c65, some c16, some c66, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p74 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked74 : lratChecker f74 p74 = .success := by decide +kernel
theorem unsat74 : Unsatisfiable (PosFin 31) f74 := by
  apply lratCheckerSound f74 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p74
  · intro a ha; simp [p74] at ha; subst a; trivial
  · exact checked74
theorem derived74 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c74 := by
  apply localUnsat_implies_entails f74 [c59, c60, c65, c16, c66] c74 unsat74 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c75 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f75 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c49, some c68, some c15, some c69, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p75 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked75 : lratChecker f75 p75 = .success := by decide +kernel
theorem unsat75 : Unsatisfiable (PosFin 31) f75 := by
  apply lratCheckerSound f75 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p75
  · intro a ha; simp [p75] at ha; subst a; trivial
  · exact checked75
theorem derived75 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c75 := by
  apply localUnsat_implies_entails f75 [c48, c49, c68, c15, c69] c75 unsat75 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c76 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f76 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c74, some c67, some c75, some c70, some c13, some c59, some c60, some c48, some c66, some c51, some c22, some c29, some c57, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p76 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked76 : lratChecker f76 p76 = .success := by decide +kernel
theorem unsat76 : Unsatisfiable (PosFin 31) f76 := by
  apply lratCheckerSound f76 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p76
  · intro a ha; simp [p76] at ha; subst a; trivial
  · exact checked76
theorem derived76 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c76 := by
  apply localUnsat_implies_entails f76 [c74, c67, c75, c70, c13, c59, c60, c48, c66, c51, c22, c29, c57] c76 unsat76 (by rfl) a
  have h0 : Entails.eval a c74 := derived74 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c75 := derived75 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c77 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f77 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c75, some c70, some c48, some c49, some c59, some c60, some c74, some c67, some c39, some c28, some c76, some c24, some c43, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p77 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked77 : lratChecker f77 p77 = .success := by decide +kernel
theorem unsat77 : Unsatisfiable (PosFin 31) f77 := by
  apply lratCheckerSound f77 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p77
  · intro a ha; simp [p77] at ha; subst a; trivial
  · exact checked77
theorem derived77 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c77 := by
  apply localUnsat_implies_entails f77 [c75, c70, c48, c49, c59, c60, c74, c67, c39, c28, c76, c24, c43] c77 unsat77 (by rfl) a
  have h0 : Entails.eval a c75 := derived75 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c74 := derived74 a h
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c76 := derived76 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c78 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f78 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c77, some c61, some c75, some c70, some c48, some c49, some c39, some c13, some c54, some c2, some c10, some c8, some c24, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p78 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked78 : lratChecker f78 p78 = .success := by decide +kernel
theorem unsat78 : Unsatisfiable (PosFin 31) f78 := by
  apply lratCheckerSound f78 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p78
  · intro a ha; simp [p78] at ha; subst a; trivial
  · exact checked78
theorem derived78 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c78 := by
  apply localUnsat_implies_entails f78 [c77, c61, c75, c70, c48, c49, c39, c13, c54, c2, c10, c8, c24] c78 unsat78 (by rfl) a
  have h0 : Entails.eval a c77 := derived77 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c75 := derived75 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c79 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f79 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c78, some c67, some c65, some c66, some c77, some c75, some c48, some c49, some c5, some c24, some c27, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p79 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked79 : lratChecker f79 p79 = .success := by decide +kernel
theorem unsat79 : Unsatisfiable (PosFin 31) f79 := by
  apply lratCheckerSound f79 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p79
  · intro a ha; simp [p79] at ha; subst a; trivial
  · exact checked79
theorem derived79 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c79 := by
  apply localUnsat_implies_entails f79 [c78, c67, c65, c66, c77, c75, c48, c49, c5, c24, c27] c79 unsat79 (by rfl) a
  have h0 : Entails.eval a c78 := derived78 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c77 := derived77 a h
  have h5 : Entails.eval a c75 := derived75 a h
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c80 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f80 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c48, some c49, some c78, some c67, some c65, some c66, some c79, some c30, some c32, some c4, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p80 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked80 : lratChecker f80 p80 = .success := by decide +kernel
theorem unsat80 : Unsatisfiable (PosFin 31) f80 := by
  apply lratCheckerSound f80 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p80
  · intro a ha; simp [p80] at ha; subst a; trivial
  · exact checked80
theorem derived80 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c80 := by
  apply localUnsat_implies_entails f80 [c48, c49, c78, c67, c65, c66, c79, c30, c32, c4] c80 unsat80 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c78 := derived78 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c79 := derived79 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c81 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f81 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c80, some c52, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p81 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked81 : lratChecker f81 p81 = .success := by decide +kernel
theorem unsat81 : Unsatisfiable (PosFin 31) f81 := by
  apply lratCheckerSound f81 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p81
  · intro a ha; simp [p81] at ha; subst a; trivial
  · exact checked81
theorem derived81 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c81 := by
  apply localUnsat_implies_entails f81 [c80, c52] c81 unsat81 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c82 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f82 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c80, some c81, some c65, some c66, some c74, some c23, some c7, some c69, some c68, some c70, some c37, some c44, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p82 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked82 : lratChecker f82 p82 = .success := by decide +kernel
theorem unsat82 : Unsatisfiable (PosFin 31) f82 := by
  apply lratCheckerSound f82 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p82
  · intro a ha; simp [p82] at ha; subst a; trivial
  · exact checked82
theorem derived82 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c82 := by
  apply localUnsat_implies_entails f82 [c80, c81, c65, c66, c74, c23, c7, c69, c68, c70, c37, c44] c82 unsat82 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c81 := derived81 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c74 := derived74 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c83 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f83 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c80, some c65, some c74, some c66, some c61, some c82, some c32, some c31, some c27, some c18, some c25, some c40, some c49, some c41, some c21, some c63, some c68, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p83 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked83 : lratChecker f83 p83 = .success := by decide +kernel
theorem unsat83 : Unsatisfiable (PosFin 31) f83 := by
  apply lratCheckerSound f83 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p83
  · intro a ha; simp [p83] at ha; subst a; trivial
  · exact checked83
theorem derived83 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c83 := by
  apply localUnsat_implies_entails f83 [c81, c80, c65, c74, c66, c61, c82, c32, c31, c27, c18, c25, c40, c49, c41, c21, c63, c68] c83 unsat83 (by rfl) a
  have h0 : Entails.eval a c81 := derived81 a h
  have h1 : Entails.eval a c80 := derived80 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c74 := derived74 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c82 := derived82 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c84 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f84 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c67, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p84 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked84 : lratChecker f84 p84 = .success := by decide +kernel
theorem unsat84 : Unsatisfiable (PosFin 31) f84 := by
  apply lratCheckerSound f84 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p84
  · intro a ha; simp [p84] at ha; subst a; trivial
  · exact checked84
theorem derived84 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c84 := by
  apply localUnsat_implies_entails f84 [c83, c67] c84 unsat84 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c85 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f85 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c81, some c61, some c35, some c68, some c70, some c5, some c12, some c44, some c37, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p85 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked85 : lratChecker f85 p85 = .success := by decide +kernel
theorem unsat85 : Unsatisfiable (PosFin 31) f85 := by
  apply lratCheckerSound f85 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p85
  · intro a ha; simp [p85] at ha; subst a; trivial
  · exact checked85
theorem derived85 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c85 := by
  apply localUnsat_implies_entails f85 [c84, c81, c61, c35, c68, c70, c5, c12, c44, c37] c85 unsat85 (by rfl) a
  have h0 : Entails.eval a c84 := derived84 a h
  have h1 : Entails.eval a c81 := derived81 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c86 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f86 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c81, some c85, some c59, some c60, some c70, some c22, some c14, some c62, some c38, some c45, some c2, some c11, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p86 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked86 : lratChecker f86 p86 = .success := by decide +kernel
theorem unsat86 : Unsatisfiable (PosFin 31) f86 := by
  apply lratCheckerSound f86 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p86
  · intro a ha; simp [p86] at ha; subst a; trivial
  · exact checked86
theorem derived86 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c86 := by
  apply localUnsat_implies_entails f86 [c84, c81, c85, c59, c60, c70, c22, c14, c62, c38, c45, c2, c11] c86 unsat86 (by rfl) a
  have h0 : Entails.eval a c84 := derived84 a h
  have h1 : Entails.eval a c81 := derived81 a h
  have h2 : Entails.eval a c85 := derived85 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c87 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f87 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c80, some c83, some c81, some c19, some c85, some c59, some c60, some c86, some c68, some c3, some c34, some c64, some c33, some c72, some c71, some c58, some c20, some c50, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p87 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked87 : lratChecker f87 p87 = .success := by decide +kernel
theorem unsat87 : Unsatisfiable (PosFin 31) f87 := by
  apply lratCheckerSound f87 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p87
  · intro a ha; simp [p87] at ha; subst a; trivial
  · exact checked87
theorem derived87 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c87 := by
  apply localUnsat_implies_entails f87 [c80, c83, c81, c19, c85, c59, c60, c86, c68, c3, c34, c64, c33, c72, c71, c58, c20, c50] c87 unsat87 (by rfl) a
  have h0 : Entails.eval a c80 := derived80 a h
  have h1 : Entails.eval a c83 := derived83 a h
  have h2 : Entails.eval a c81 := derived81 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c85 := derived85 a h
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c86 := derived86 a h
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c58 := h 57 (by decide)
  have h16 : Entails.eval a c20 := h 19 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c88 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f88 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c80, some c87, some c29, some c6, some c26, some c28, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p88 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked88 : lratChecker f88 p88 = .success := by decide +kernel
theorem unsat88 : Unsatisfiable (PosFin 31) f88 := by
  apply lratCheckerSound f88 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p88
  · intro a ha; simp [p88] at ha; subst a; trivial
  · exact checked88
theorem derived88 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c88 := by
  apply localUnsat_implies_entails f88 [c83, c80, c87, c29, c6, c26, c28] c88 unsat88 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c80 := derived80 a h
  have h2 : Entails.eval a c87 := derived87 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c89 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f89 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c59, some c60, some c88, some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p89 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked89 : lratChecker f89 p89 = .success := by decide +kernel
theorem unsat89 : Unsatisfiable (PosFin 31) f89 := by
  apply lratCheckerSound f89 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p89
  · intro a ha; simp [p89] at ha; subst a; trivial
  · exact checked89
theorem derived89 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c89 := by
  apply localUnsat_implies_entails f89 [c59, c60, c88] c89 unsat89 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c88 := derived88 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c90 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f90 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c89, some c61, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p90 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked90 : lratChecker f90 p90 = .success := by decide +kernel
theorem unsat90 : Unsatisfiable (PosFin 31) f90 := by
  apply lratCheckerSound f90 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p90
  · intro a ha; simp [p90] at ha; subst a; trivial
  · exact checked90
theorem derived90 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c90 := by
  apply localUnsat_implies_entails f90 [c89, c61] c90 unsat90 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c91 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f91 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c89, some c84, some c80, some c53, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p91 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked91 : lratChecker f91 p91 = .success := by decide +kernel
theorem unsat91 : Unsatisfiable (PosFin 31) f91 := by
  apply lratCheckerSound f91 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p91
  · intro a ha; simp [p91] at ha; subst a; trivial
  · exact checked91
theorem derived91 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c91 := by
  apply localUnsat_implies_entails f91 [c89, c84, c80, c53] c91 unsat91 (by rfl) a
  have h0 : Entails.eval a c89 := derived89 a h
  have h1 : Entails.eval a c84 := derived84 a h
  have h2 : Entails.eval a c80 := derived80 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c92 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f92 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c84, some c87, some c81, some c90, some c80, some c89, some c91, some c6, some c43, some c10, some c37, some c36, some c55, some c2, some c73, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p92 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked92 : lratChecker f92 p92 = .success := by decide +kernel
theorem unsat92 : Unsatisfiable (PosFin 31) f92 := by
  apply lratCheckerSound f92 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p92
  · intro a ha; simp [p92] at ha; subst a; trivial
  · exact checked92
theorem derived92 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c92 := by
  apply localUnsat_implies_entails f92 [c83, c84, c87, c81, c90, c80, c89, c91, c6, c43, c10, c37, c36, c55, c2, c73] c92 unsat92 (by rfl) a
  have h0 : Entails.eval a c83 := derived83 a h
  have h1 : Entails.eval a c84 := derived84 a h
  have h2 : Entails.eval a c87 := derived87 a h
  have h3 : Entails.eval a c81 := derived81 a h
  have h4 : Entails.eval a c90 := derived90 a h
  have h5 : Entails.eval a c80 := derived80 a h
  have h6 : Entails.eval a c89 := derived89 a h
  have h7 : Entails.eval a c91 := derived91 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c93 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f93 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c92, some c81, some c87, some c42, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p93 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked93 : lratChecker f93 p93 = .success := by decide +kernel
theorem unsat93 : Unsatisfiable (PosFin 31) f93 := by
  apply lratCheckerSound f93 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p93
  · intro a ha; simp [p93] at ha; subst a; trivial
  · exact checked93
theorem derived93 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c93 := by
  apply localUnsat_implies_entails f93 [c92, c81, c87, c42] c93 unsat93 (by rfl) a
  have h0 : Entails.eval a c92 := derived92 a h
  have h1 : Entails.eval a c81 := derived81 a h
  have h2 : Entails.eval a c87 := derived87 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c94 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f94 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c92, some c87, some c9, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p94 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked94 : lratChecker f94 p94 = .success := by decide +kernel
theorem unsat94 : Unsatisfiable (PosFin 31) f94 := by
  apply lratCheckerSound f94 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p94
  · intro a ha; simp [p94] at ha; subst a; trivial
  · exact checked94
theorem derived94 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c94 := by
  apply localUnsat_implies_entails f94 [c92, c87, c9] c94 unsat94 (by rfl) a
  have h0 : Entails.eval a c92 := derived92 a h
  have h1 : Entails.eval a c87 := derived87 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c95 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f95 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c93, some c49, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p95 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked95 : lratChecker f95 p95 = .success := by decide +kernel
theorem unsat95 : Unsatisfiable (PosFin 31) f95 := by
  apply lratCheckerSound f95 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p95
  · intro a ha; simp [p95] at ha; subst a; trivial
  · exact checked95
theorem derived95 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c95 := by
  apply localUnsat_implies_entails f95 [c93, c49] c95 unsat95 (by rfl) a
  have h0 : Entails.eval a c93 := derived93 a h
  have h1 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c96 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f96 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c91, some c1, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p96 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked96 : lratChecker f96 p96 = .success := by decide +kernel
theorem unsat96 : Unsatisfiable (PosFin 31) f96 := by
  apply lratCheckerSound f96 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p96
  · intro a ha; simp [p96] at ha; subst a; trivial
  · exact checked96
theorem derived96 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c96 := by
  apply localUnsat_implies_entails f96 [c94, c91, c1] c96 unsat96 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c91 := derived91 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c97 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c91, some c2, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p97 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 31) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c94, c91, c2] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c91 := derived91 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c98 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c96, some c95, some c17, some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p98 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 31) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c96, c95, c17] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c95 := derived95 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c99 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c96, some c93, some c90, some c84, some c97, some c56, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p99 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 31) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c96, c93, c90, c84, c97, c56] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c93 := derived93 a h
  have h2 : Entails.eval a c90 := derived90 a h
  have h3 : Entails.eval a c84 := derived84 a h
  have h4 : Entails.eval a c97 := derived97 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c100 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c96, some c87, some c90, some c92, some c95, some c46, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p100 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 31) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c96, c87, c90, c92, c95, c46] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c87 := derived87 a h
  have h2 : Entails.eval a c90 := derived90 a h
  have h3 : Entails.eval a c92 := derived92 a h
  have h4 : Entails.eval a c95 := derived95 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c101 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f101 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c100, some c98, some c87, some c99, some c47]
def p101 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked101 : lratChecker f101 p101 = .success := by decide +kernel
theorem unsat101 : Unsatisfiable (PosFin 31) f101 := by
  apply lratCheckerSound f101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p101
  · intro a ha; simp [p101] at ha; subst a; trivial
  · exact checked101
theorem derived101 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c101 := by
  apply localUnsat_implies_entails f101 [c100, c98, c87, c99, c47] c101 unsat101 (by rfl) a
  have h0 : Entails.eval a c100 := derived100 a h
  have h1 : Entails.eval a c98 := derived98 a h
  have h2 : Entails.eval a c87 := derived87 a h
  have h3 : Entails.eval a c99 := derived99 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived101

end CochromaticTwenty.Certificates.Z12Direct_5_2_6
