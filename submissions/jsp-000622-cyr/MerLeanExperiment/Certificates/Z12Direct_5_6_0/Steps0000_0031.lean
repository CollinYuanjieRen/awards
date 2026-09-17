import MerLeanExperiment.Certificates.Z12Direct_5_6_0.Inputs

/-! Generated from the actual pinned z12direct_5_6_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_6_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c80 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f80 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c13, some c15, some c19, some c21, some c74, some c79, some c36, some c28, some c38, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p80 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked80 : lratChecker f80 p80 = .success := by decide +kernel
theorem unsat80 : Unsatisfiable (PosFin 31) f80 := by
  apply lratCheckerSound f80 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p80
  · intro a ha; simp [p80] at ha; subst a; trivial
  · exact checked80
theorem derived80 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c80 := by
  apply localUnsat_implies_entails f80 [c13, c15, c19, c21, c74, c79, c36, c28, c38] c80 unsat80 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c81 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f81 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c69, some c65, some c74, some c79, some c8, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p81 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked81 : lratChecker f81 p81 = .success := by decide +kernel
theorem unsat81 : Unsatisfiable (PosFin 31) f81 := by
  apply lratCheckerSound f81 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p81
  · intro a ha; simp [p81] at ha; subst a; trivial
  · exact checked81
theorem derived81 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c81 := by
  apply localUnsat_implies_entails f81 [c69, c65, c74, c79, c8] c81 unsat81 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c82 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f82 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c65, some c69, some c22, some c81, some c14, some c27, some c20, some c35, some c37, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p82 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked82 : lratChecker f82 p82 = .success := by decide +kernel
theorem unsat82 : Unsatisfiable (PosFin 31) f82 := by
  apply lratCheckerSound f82 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p82
  · intro a ha; simp [p82] at ha; subst a; trivial
  · exact checked82
theorem derived82 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c82 := by
  apply localUnsat_implies_entails f82 [c65, c69, c22, c81, c14, c27, c20, c35, c37] c82 unsat82 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c81 := derived81 a h
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c83 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f83 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c36, some c26, some c2, some c4, some c39, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p83 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked83 : lratChecker f83 p83 = .success := by decide +kernel
theorem unsat83 : Unsatisfiable (PosFin 31) f83 := by
  apply lratCheckerSound f83 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p83
  · intro a ha; simp [p83] at ha; subst a; trivial
  · exact checked83
theorem derived83 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c83 := by
  apply localUnsat_implies_entails f83 [c36, c26, c2, c4, c39] c83 unsat83 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c84 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f84 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c18, some c82, some c15, some c80, some c74, some c79, some c83, some c38, some c34, some c1, some c3, some c7, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p84 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked84 : lratChecker f84 p84 = .success := by decide +kernel
theorem unsat84 : Unsatisfiable (PosFin 31) f84 := by
  apply lratCheckerSound f84 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p84
  · intro a ha; simp [p84] at ha; subst a; trivial
  · exact checked84
theorem derived84 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c84 := by
  apply localUnsat_implies_entails f84 [c18, c82, c15, c80, c74, c79, c83, c38, c34, c1, c3, c7] c84 unsat84 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c82 := derived82 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c80 := derived80 a h
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c83 := derived83 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c85 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f85 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c15, some c74, some c79, some c83, some c38, some c34, some c25, some c54, some c32, some c70, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p85 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked85 : lratChecker f85 p85 = .success := by decide +kernel
theorem unsat85 : Unsatisfiable (PosFin 31) f85 := by
  apply lratCheckerSound f85 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p85
  · intro a ha; simp [p85] at ha; subst a; trivial
  · exact checked85
theorem derived85 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c85 := by
  apply localUnsat_implies_entails f85 [c84, c15, c74, c79, c83, c38, c34, c25, c54, c32, c70] c85 unsat85 (by rfl) a
  have h0 : Entails.eval a c84 := derived84 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c83 := derived83 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c86 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f86 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c24, some c37, some c44, some c35, some c60, some c33, some c31, some c75, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p86 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked86 : lratChecker f86 p86 = .success := by decide +kernel
theorem unsat86 : Unsatisfiable (PosFin 31) f86 := by
  apply lratCheckerSound f86 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p86
  · intro a ha; simp [p86] at ha; subst a; trivial
  · exact checked86
theorem derived86 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c86 := by
  apply localUnsat_implies_entails f86 [c24, c37, c44, c35, c60, c33, c31, c75] c86 unsat86 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c87 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨12, by decide⟩, false), (⟨29, by decide⟩, false), (⟨18, by decide⟩, false), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f87 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c86, some c6, some c29, some c27, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p87 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked87 : lratChecker f87 p87 = .success := by decide +kernel
theorem unsat87 : Unsatisfiable (PosFin 31) f87 := by
  apply lratCheckerSound f87 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p87
  · intro a ha; simp [p87] at ha; subst a; trivial
  · exact checked87
theorem derived87 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c87 := by
  apply localUnsat_implies_entails f87 [c86, c6, c29, c27] c87 unsat87 (by rfl) a
  have h0 : Entails.eval a c86 := derived86 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c88 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f88 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c85, some c65, some c69, some c81, some c87, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p88 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked88 : lratChecker f88 p88 = .success := by decide +kernel
theorem unsat88 : Unsatisfiable (PosFin 31) f88 := by
  apply lratCheckerSound f88 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p88
  · intro a ha; simp [p88] at ha; subst a; trivial
  · exact checked88
theorem derived88 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c88 := by
  apply localUnsat_implies_entails f88 [c84, c85, c65, c69, c81, c87] c88 unsat88 (by rfl) a
  have h0 : Entails.eval a c84 := derived84 a h
  have h1 : Entails.eval a c85 := derived85 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c81 := derived81 a h
  have h5 : Entails.eval a c87 := derived87 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c89 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f89 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c88, some c80, some c81, some c69, some c65, some c27, some c35, some c19, some c30, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p89 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked89 : lratChecker f89 p89 = .success := by decide +kernel
theorem unsat89 : Unsatisfiable (PosFin 31) f89 := by
  apply lratCheckerSound f89 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p89
  · intro a ha; simp [p89] at ha; subst a; trivial
  · exact checked89
theorem derived89 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c89 := by
  apply localUnsat_implies_entails f89 [c88, c80, c81, c69, c65, c27, c35, c19, c30] c89 unsat89 (by rfl) a
  have h0 : Entails.eval a c88 := derived88 a h
  have h1 : Entails.eval a c80 := derived80 a h
  have h2 : Entails.eval a c81 := derived81 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c90 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f90 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c88, some c17, some c80, some c65, some c69, some c81, some c89, some c29, some c24, some c5, some c23, some c61, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p90 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked90 : lratChecker f90 p90 = .success := by decide +kernel
theorem unsat90 : Unsatisfiable (PosFin 31) f90 := by
  apply lratCheckerSound f90 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p90
  · intro a ha; simp [p90] at ha; subst a; trivial
  · exact checked90
theorem derived90 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c90 := by
  apply localUnsat_implies_entails f90 [c88, c17, c80, c65, c69, c81, c89, c29, c24, c5, c23, c61] c90 unsat90 (by rfl) a
  have h0 : Entails.eval a c88 := derived88 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c80 := derived80 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c81 := derived81 a h
  have h6 : Entails.eval a c89 := derived89 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c91 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f91 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c76, some c10, some c78, some c48, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p91 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked91 : lratChecker f91 p91 = .success := by decide +kernel
theorem unsat91 : Unsatisfiable (PosFin 31) f91 := by
  apply lratCheckerSound f91 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p91
  · intro a ha; simp [p91] at ha; subst a; trivial
  · exact checked91
theorem derived91 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c91 := by
  apply localUnsat_implies_entails f91 [c76, c10, c78, c48] c91 unsat91 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c92 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f92 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c76, some c71, some c91, some c58, some c8, some c53, some c12, some c73, some c45, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p92 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked92 : lratChecker f92 p92 = .success := by decide +kernel
theorem unsat92 : Unsatisfiable (PosFin 31) f92 := by
  apply lratCheckerSound f92 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p92
  · intro a ha; simp [p92] at ha; subst a; trivial
  · exact checked92
theorem derived92 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c92 := by
  apply localUnsat_implies_entails f92 [c76, c71, c91, c58, c8, c53, c12, c73, c45] c92 unsat92 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c91 := derived91 a h
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c93 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f93 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c90, some c92, some c17, some c71, some c52, some c40, some c64, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p93 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked93 : lratChecker f93 p93 = .success := by decide +kernel
theorem unsat93 : Unsatisfiable (PosFin 31) f93 := by
  apply lratCheckerSound f93 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p93
  · intro a ha; simp [p93] at ha; subst a; trivial
  · exact checked93
theorem derived93 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c93 := by
  apply localUnsat_implies_entails f93 [c90, c92, c17, c71, c52, c40, c64] c93 unsat93 (by rfl) a
  have h0 : Entails.eval a c90 := derived90 a h
  have h1 : Entails.eval a c92 := derived92 a h
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c94 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f94 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c90, some c71, some c76, some c92, some c17, some c57, some c93, some c8, some c42, some c68, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p94 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked94 : lratChecker f94 p94 = .success := by decide +kernel
theorem unsat94 : Unsatisfiable (PosFin 31) f94 := by
  apply lratCheckerSound f94 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p94
  · intro a ha; simp [p94] at ha; subst a; trivial
  · exact checked94
theorem derived94 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c94 := by
  apply localUnsat_implies_entails f94 [c90, c71, c76, c92, c17, c57, c93, c8, c42, c68] c94 unsat94 (by rfl) a
  have h0 : Entails.eval a c90 := derived90 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c92 := derived92 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c93 := derived93 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c95 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f95 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c62, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p95 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked95 : lratChecker f95 p95 = .success := by decide +kernel
theorem unsat95 : Unsatisfiable (PosFin 31) f95 := by
  apply lratCheckerSound f95 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p95
  · intro a ha; simp [p95] at ha; subst a; trivial
  · exact checked95
theorem derived95 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c95 := by
  apply localUnsat_implies_entails f95 [c94, c62] c95 unsat95 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c96 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f96 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c66, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p96 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked96 : lratChecker f96 p96 = .success := by decide +kernel
theorem unsat96 : Unsatisfiable (PosFin 31) f96 := by
  apply lratCheckerSound f96 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p96
  · intro a ha; simp [p96] at ha; subst a; trivial
  · exact checked96
theorem derived96 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c96 := by
  apply localUnsat_implies_entails f96 [c94, c66] c96 unsat96 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c97 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f97 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c96, some c95, some c8, some c59, some c71, some c74, some c50, some c87, some c11, some c46, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p97 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked97 : lratChecker f97 p97 = .success := by decide +kernel
theorem unsat97 : Unsatisfiable (PosFin 31) f97 := by
  apply lratCheckerSound f97 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p97
  · intro a ha; simp [p97] at ha; subst a; trivial
  · exact checked97
theorem derived97 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c97 := by
  apply localUnsat_implies_entails f97 [c94, c96, c95, c8, c59, c71, c74, c50, c87, c11, c46] c97 unsat97 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c95 := derived95 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c87 := derived87 a h
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c98 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f98 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c96, some c94, some c95, some c97, some c76, some c79, some c87, some c18, some c49, some c55, some c9, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p98 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked98 : lratChecker f98 p98 = .success := by decide +kernel
theorem unsat98 : Unsatisfiable (PosFin 31) f98 := by
  apply lratCheckerSound f98 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p98
  · intro a ha; simp [p98] at ha; subst a; trivial
  · exact checked98
theorem derived98 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c98 := by
  apply localUnsat_implies_entails f98 [c96, c94, c95, c97, c76, c79, c87, c18, c49, c55, c9] c98 unsat98 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c94 := derived94 a h
  have h2 : Entails.eval a c95 := derived95 a h
  have h3 : Entails.eval a c97 := derived97 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c87 := derived87 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c99 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f99 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c96, some c95, some c94, some c98, some c92, some c79, some c87, some c18, some c55, some c47, some c67, some c43, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p99 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked99 : lratChecker f99 p99 = .success := by decide +kernel
theorem unsat99 : Unsatisfiable (PosFin 31) f99 := by
  apply lratCheckerSound f99 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p99
  · intro a ha; simp [p99] at ha; subst a; trivial
  · exact checked99
theorem derived99 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c99 := by
  apply localUnsat_implies_entails f99 [c96, c95, c94, c98, c92, c79, c87, c18, c55, c47, c67, c43] c99 unsat99 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c95 := derived95 a h
  have h2 : Entails.eval a c94 := derived94 a h
  have h3 : Entails.eval a c98 := derived98 a h
  have h4 : Entails.eval a c92 := derived92 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c87 := derived87 a h
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c100 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f100 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c95, some c50, some c11, some c63, some c41, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p100 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked100 : lratChecker f100 p100 = .success := by decide +kernel
theorem unsat100 : Unsatisfiable (PosFin 31) f100 := by
  apply lratCheckerSound f100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p100
  · intro a ha; simp [p100] at ha; subst a; trivial
  · exact checked100
theorem derived100 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c100 := by
  apply localUnsat_implies_entails f100 [c94, c95, c50, c11, c63, c41] c100 unsat100 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c95 := derived95 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c101 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f101 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c96, some c95, some c98, some c92, some c99, some c8, some c74, some c87, some c18, some c100, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p101 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked101 : lratChecker f101 p101 = .success := by decide +kernel
theorem unsat101 : Unsatisfiable (PosFin 31) f101 := by
  apply lratCheckerSound f101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p101
  · intro a ha; simp [p101] at ha; subst a; trivial
  · exact checked101
theorem derived101 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c101 := by
  apply localUnsat_implies_entails f101 [c96, c95, c98, c92, c99, c8, c74, c87, c18, c100] c101 unsat101 (by rfl) a
  have h0 : Entails.eval a c96 := derived96 a h
  have h1 : Entails.eval a c95 := derived95 a h
  have h2 : Entails.eval a c98 := derived98 a h
  have h3 : Entails.eval a c92 := derived92 a h
  have h4 : Entails.eval a c99 := derived99 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c87 := derived87 a h
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c100 := derived100 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c102 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f102 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c96, some c67, some c9, some c43, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p102 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked102 : lratChecker f102 p102 = .success := by decide +kernel
theorem unsat102 : Unsatisfiable (PosFin 31) f102 := by
  apply lratCheckerSound f102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p102
  · intro a ha; simp [p102] at ha; subst a; trivial
  · exact checked102
theorem derived102 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c102 := by
  apply localUnsat_implies_entails f102 [c94, c96, c67, c9, c43] c102 unsat102 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c103 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f103 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c94, some c55, some c102, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p103 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked103 : lratChecker f103 p103 = .success := by decide +kernel
theorem unsat103 : Unsatisfiable (PosFin 31) f103 := by
  apply lratCheckerSound f103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p103
  · intro a ha; simp [p103] at ha; subst a; trivial
  · exact checked103
theorem derived103 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c103 := by
  apply localUnsat_implies_entails f103 [c94, c55, c102] c103 unsat103 (by rfl) a
  have h0 : Entails.eval a c94 := derived94 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c102 := derived102 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c104 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f104 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c95, some c96, some c100, some c8, some c103, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p104 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked104 : lratChecker f104 p104 = .success := by decide +kernel
theorem unsat104 : Unsatisfiable (PosFin 31) f104 := by
  apply lratCheckerSound f104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p104
  · intro a ha; simp [p104] at ha; subst a; trivial
  · exact checked104
theorem derived104 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c104 := by
  apply localUnsat_implies_entails f104 [c95, c96, c100, c8, c103] c104 unsat104 (by rfl) a
  have h0 : Entails.eval a c95 := derived95 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c100 := derived100 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c103 := derived103 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c105 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f105 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c104, some c101, some c16, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p105 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked105 : lratChecker f105 p105 = .success := by decide +kernel
theorem unsat105 : Unsatisfiable (PosFin 31) f105 := by
  apply lratCheckerSound f105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p105
  · intro a ha; simp [p105] at ha; subst a; trivial
  · exact checked105
theorem derived105 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c105 := by
  apply localUnsat_implies_entails f105 [c104, c101, c16] c105 unsat105 (by rfl) a
  have h0 : Entails.eval a c104 := derived104 a h
  have h1 : Entails.eval a c101 := derived101 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c106 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f106 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c105, some c92, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p106 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked106 : lratChecker f106 p106 = .success := by decide +kernel
theorem unsat106 : Unsatisfiable (PosFin 31) f106 := by
  apply lratCheckerSound f106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p106
  · intro a ha; simp [p106] at ha; subst a; trivial
  · exact checked106
theorem derived106 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c106 := by
  apply localUnsat_implies_entails f106 [c105, c92] c106 unsat106 (by rfl) a
  have h0 : Entails.eval a c105 := derived105 a h
  have h1 : Entails.eval a c92 := derived92 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c107 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f107 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c106, some c96, some c104, some c56, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p107 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked107 : lratChecker f107 p107 = .success := by decide +kernel
theorem unsat107 : Unsatisfiable (PosFin 31) f107 := by
  apply lratCheckerSound f107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p107
  · intro a ha; simp [p107] at ha; subst a; trivial
  · exact checked107
theorem derived107 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c107 := by
  apply localUnsat_implies_entails f107 [c106, c96, c104, c56] c107 unsat107 (by rfl) a
  have h0 : Entails.eval a c106 := derived106 a h
  have h1 : Entails.eval a c96 := derived96 a h
  have h2 : Entails.eval a c104 := derived104 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c108 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f108 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c106, some c95, some c104, some c51, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p108 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked108 : lratChecker f108 p108 = .success := by decide +kernel
theorem unsat108 : Unsatisfiable (PosFin 31) f108 := by
  apply lratCheckerSound f108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p108
  · intro a ha; simp [p108] at ha; subst a; trivial
  · exact checked108
theorem derived108 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c108 := by
  apply localUnsat_implies_entails f108 [c106, c95, c104, c51] c108 unsat108 (by rfl) a
  have h0 : Entails.eval a c106 := derived106 a h
  have h1 : Entails.eval a c95 := derived95 a h
  have h2 : Entails.eval a c104 := derived104 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c109 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f109 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c107, some c104, some c101, some c77, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p109 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked109 : lratChecker f109 p109 = .success := by decide +kernel
theorem unsat109 : Unsatisfiable (PosFin 31) f109 := by
  apply lratCheckerSound f109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p109
  · intro a ha; simp [p109] at ha; subst a; trivial
  · exact checked109
theorem derived109 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c109 := by
  apply localUnsat_implies_entails f109 [c107, c104, c101, c77] c109 unsat109 (by rfl) a
  have h0 : Entails.eval a c107 := derived107 a h
  have h1 : Entails.eval a c104 := derived104 a h
  have h2 : Entails.eval a c101 := derived101 a h
  have h3 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c110 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f110 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c108, some c104, some c101, some c72, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p110 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked110 : lratChecker f110 p110 = .success := by decide +kernel
theorem unsat110 : Unsatisfiable (PosFin 31) f110 := by
  apply lratCheckerSound f110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p110
  · intro a ha; simp [p110] at ha; subst a; trivial
  · exact checked110
theorem derived110 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c110 := by
  apply localUnsat_implies_entails f110 [c108, c104, c101, c72] c110 unsat110 (by rfl) a
  have h0 : Entails.eval a c108 := derived108 a h
  have h1 : Entails.eval a c104 := derived104 a h
  have h2 : Entails.eval a c101 := derived101 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c111 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f111 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c109, some c110, some c96, some c95, some c8]
def p111 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked111 : lratChecker f111 p111 = .success := by decide +kernel
theorem unsat111 : Unsatisfiable (PosFin 31) f111 := by
  apply lratCheckerSound f111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p111
  · intro a ha; simp [p111] at ha; subst a; trivial
  · exact checked111
theorem derived111 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c111 := by
  apply localUnsat_implies_entails f111 [c109, c110, c96, c95, c8] c111 unsat111 (by rfl) a
  have h0 : Entails.eval a c109 := derived109 a h
  have h1 : Entails.eval a c110 := derived110 a h
  have h2 : Entails.eval a c96 := derived96 a h
  have h3 : Entails.eval a c95 := derived95 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived111

end CochromaticTwenty.Certificates.Z12Direct_5_6_0
