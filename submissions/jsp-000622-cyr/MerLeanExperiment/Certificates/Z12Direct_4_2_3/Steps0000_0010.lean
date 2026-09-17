import MerLeanExperiment.Certificates.Z12Direct_4_2_3.Inputs

/-! Generated from the actual pinned z12direct_4_2_3-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_3
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c20 : DefaultClause 29 := directClause [(⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f20 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c7, some c10, some c3, some c1, some c15, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p20 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked20 : lratChecker f20 p20 = .success := by decide +kernel
theorem unsat20 : Unsatisfiable (PosFin 29) f20 := by
  apply lratCheckerSound f20 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p20
  · intro a ha; simp [p20] at ha; subst a; trivial
  · exact checked20
theorem derived20 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c20 := by
  apply localUnsat_implies_entails f20 [c7, c10, c3, c1, c15] c20 unsat20 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c21 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false), (⟨26, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f21 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c5, some c9, some c12, some c3, some c1, some c13, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p21 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked21 : lratChecker f21 p21 = .success := by decide +kernel
theorem unsat21 : Unsatisfiable (PosFin 29) f21 := by
  apply lratCheckerSound f21 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p21
  · intro a ha; simp [p21] at ha; subst a; trivial
  · exact checked21
theorem derived21 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c21 := by
  apply localUnsat_implies_entails f21 [c5, c9, c12, c3, c1, c13] c21 unsat21 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c22 : DefaultClause 29 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f22 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c20, some c21, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p22 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked22 : lratChecker f22 p22 = .success := by decide +kernel
theorem unsat22 : Unsatisfiable (PosFin 29) f22 := by
  apply lratCheckerSound f22 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p22
  · intro a ha; simp [p22] at ha; subst a; trivial
  · exact checked22
theorem derived22 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c22 := by
  apply localUnsat_implies_entails f22 [c20, c21] c22 unsat22 (by rfl) a
  have h0 : Entails.eval a c20 := derived20 a h
  have h1 : Entails.eval a c21 := derived21 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c23 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f23 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c9, some c12, some c4, some c2, some c14, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p23 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked23 : lratChecker f23 p23 = .success := by decide +kernel
theorem unsat23 : Unsatisfiable (PosFin 29) f23 := by
  apply lratCheckerSound f23 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p23
  · intro a ha; simp [p23] at ha; subst a; trivial
  · exact checked23
theorem derived23 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c23 := by
  apply localUnsat_implies_entails f23 [c9, c12, c4, c2, c14] c23 unsat23 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c24 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f24 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c6, some c8, some c11, some c4, some c2, some c15, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p24 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked24 : lratChecker f24 p24 = .success := by decide +kernel
theorem unsat24 : Unsatisfiable (PosFin 29) f24 := by
  apply lratCheckerSound f24 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p24
  · intro a ha; simp [p24] at ha; subst a; trivial
  · exact checked24
theorem derived24 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c24 := by
  apply localUnsat_implies_entails f24 [c6, c8, c11, c4, c2, c15] c24 unsat24 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c25 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f25 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c23, some c24, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p25 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked25 : lratChecker f25 p25 = .success := by decide +kernel
theorem unsat25 : Unsatisfiable (PosFin 29) f25 := by
  apply lratCheckerSound f25 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p25
  · intro a ha; simp [p25] at ha; subst a; trivial
  · exact checked25
theorem derived25 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c25 := by
  apply localUnsat_implies_entails f25 [c23, c24] c25 unsat25 (by rfl) a
  have h0 : Entails.eval a c23 := derived23 a h
  have h1 : Entails.eval a c24 := derived24 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c26 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f26 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c22, some c25, some c16, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p26 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked26 : lratChecker f26 p26 = .success := by decide +kernel
theorem unsat26 : Unsatisfiable (PosFin 29) f26 := by
  apply lratCheckerSound f26 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p26
  · intro a ha; simp [p26] at ha; subst a; trivial
  · exact checked26
theorem derived26 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c26 := by
  apply localUnsat_implies_entails f26 [c22, c25, c16] c26 unsat26 (by rfl) a
  have h0 : Entails.eval a c22 := derived22 a h
  have h1 : Entails.eval a c25 := derived25 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c27 : DefaultClause 29 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f27 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c26, some c19, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p27 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked27 : lratChecker f27 p27 = .success := by decide +kernel
theorem unsat27 : Unsatisfiable (PosFin 29) f27 := by
  apply lratCheckerSound f27 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p27
  · intro a ha; simp [p27] at ha; subst a; trivial
  · exact checked27
theorem derived27 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c27 := by
  apply localUnsat_implies_entails f27 [c26, c19] c27 unsat27 (by rfl) a
  have h0 : Entails.eval a c26 := derived26 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c28 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f28 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c27, some c17, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p28 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked28 : lratChecker f28 p28 = .success := by decide +kernel
theorem unsat28 : Unsatisfiable (PosFin 29) f28 := by
  apply lratCheckerSound f28 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p28
  · intro a ha; simp [p28] at ha; subst a; trivial
  · exact checked28
theorem derived28 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c28 := by
  apply localUnsat_implies_entails f28 [c27, c17] c28 unsat28 (by rfl) a
  have h0 : Entails.eval a c27 := derived27 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c29 : DefaultClause 29 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f29 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c27, some c18, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p29 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked29 : lratChecker f29 p29 = .success := by decide +kernel
theorem unsat29 : Unsatisfiable (PosFin 29) f29 := by
  apply lratCheckerSound f29 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p29
  · intro a ha; simp [p29] at ha; subst a; trivial
  · exact checked29
theorem derived29 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c29 := by
  apply localUnsat_implies_entails f29 [c27, c18] c29 unsat29 (by rfl) a
  have h0 : Entails.eval a c27 := derived27 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c30 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f30 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c29, some c28, some c16]
def p30 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked30 : lratChecker f30 p30 = .success := by decide +kernel
theorem unsat30 : Unsatisfiable (PosFin 29) f30 := by
  apply lratCheckerSound f30 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p30
  · intro a ha; simp [p30] at ha; subst a; trivial
  · exact checked30
theorem derived30 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c30 := by
  apply localUnsat_implies_entails f30 [c29, c28, c16] c30 unsat30 (by rfl) a
  have h0 : Entails.eval a c29 := derived29 a h
  have h1 : Entails.eval a c28 := derived28 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived30

end CochromaticTwenty.Certificates.Z12Direct_4_2_3
