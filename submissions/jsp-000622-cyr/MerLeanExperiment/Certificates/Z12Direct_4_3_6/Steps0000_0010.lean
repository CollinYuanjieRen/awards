import MerLeanExperiment.Certificates.Z12Direct_4_3_6.Inputs

/-! Generated from the actual pinned z12direct_4_3_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_3_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c27 : DefaultClause 29 := directClause [(⟨4, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f27 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c16, some c12, some c14, some c19, some c6, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p27 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked27 : lratChecker f27 p27 = .success := by decide +kernel
theorem unsat27 : Unsatisfiable (PosFin 29) f27 := by
  apply lratCheckerSound f27 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p27
  · intro a ha; simp [p27] at ha; subst a; trivial
  · exact checked27
theorem derived27 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c27 := by
  apply localUnsat_implies_entails f27 [c16, c12, c14, c19, c6] c27 unsat27 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c28 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f28 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c16, some c12, some c27, some c1, some c13, some c23, some c5, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p28 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked28 : lratChecker f28 p28 = .success := by decide +kernel
theorem unsat28 : Unsatisfiable (PosFin 29) f28 := by
  apply lratCheckerSound f28 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p28
  · intro a ha; simp [p28] at ha; subst a; trivial
  · exact checked28
theorem derived28 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c28 := by
  apply localUnsat_implies_entails f28 [c16, c12, c27, c1, c13, c23, c5] c28 unsat28 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c27 := derived27 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c29 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f29 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c28, some c8, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p29 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked29 : lratChecker f29 p29 = .success := by decide +kernel
theorem unsat29 : Unsatisfiable (PosFin 29) f29 := by
  apply lratCheckerSound f29 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p29
  · intro a ha; simp [p29] at ha; subst a; trivial
  · exact checked29
theorem derived29 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c29 := by
  apply localUnsat_implies_entails f29 [c28, c8] c29 unsat29 (by rfl) a
  have h0 : Entails.eval a c28 := derived28 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c30 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f30 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c28, some c13, some c5, some c4, some c15, some c25, some c11, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p30 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked30 : lratChecker f30 p30 = .success := by decide +kernel
theorem unsat30 : Unsatisfiable (PosFin 29) f30 := by
  apply lratCheckerSound f30 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p30
  · intro a ha; simp [p30] at ha; subst a; trivial
  · exact checked30
theorem derived30 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c30 := by
  apply localUnsat_implies_entails f30 [c28, c13, c5, c4, c15, c25, c11] c30 unsat30 (by rfl) a
  have h0 : Entails.eval a c28 := derived28 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c31 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f31 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c30, some c9, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p31 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked31 : lratChecker f31 p31 = .success := by decide +kernel
theorem unsat31 : Unsatisfiable (PosFin 29) f31 := by
  apply lratCheckerSound f31 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p31
  · intro a ha; simp [p31] at ha; subst a; trivial
  · exact checked31
theorem derived31 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c31 := by
  apply localUnsat_implies_entails f31 [c30, c9] c31 unsat31 (by rfl) a
  have h0 : Entails.eval a c30 := derived30 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c32 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f32 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c28, some c30, some c29, some c31, some c1, some c2, some c15, some c18, some c7, some c17, some c21, some c22, some c26, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p32 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked32 : lratChecker f32 p32 = .success := by decide +kernel
theorem unsat32 : Unsatisfiable (PosFin 29) f32 := by
  apply lratCheckerSound f32 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p32
  · intro a ha; simp [p32] at ha; subst a; trivial
  · exact checked32
theorem derived32 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c32 := by
  apply localUnsat_implies_entails f32 [c28, c30, c29, c31, c1, c2, c15, c18, c7, c17, c21, c22, c26] c32 unsat32 (by rfl) a
  have h0 : Entails.eval a c28 := derived28 a h
  have h1 : Entails.eval a c30 := derived30 a h
  have h2 : Entails.eval a c29 := derived29 a h
  have h3 : Entails.eval a c31 := derived31 a h
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c33 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f33 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c29, some c31, some c24, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p33 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked33 : lratChecker f33 p33 = .success := by decide +kernel
theorem unsat33 : Unsatisfiable (PosFin 29) f33 := by
  apply lratCheckerSound f33 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p33
  · intro a ha; simp [p33] at ha; subst a; trivial
  · exact checked33
theorem derived33 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c33 := by
  apply localUnsat_implies_entails f33 [c32, c29, c31, c24] c33 unsat33 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c29 := derived29 a h
  have h2 : Entails.eval a c31 := derived31 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c34 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f34 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c33, some c28, some c3, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p34 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked34 : lratChecker f34 p34 = .success := by decide +kernel
theorem unsat34 : Unsatisfiable (PosFin 29) f34 := by
  apply lratCheckerSound f34 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p34
  · intro a ha; simp [p34] at ha; subst a; trivial
  · exact checked34
theorem derived34 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c34 := by
  apply localUnsat_implies_entails f34 [c33, c28, c3] c34 unsat34 (by rfl) a
  have h0 : Entails.eval a c33 := derived33 a h
  have h1 : Entails.eval a c28 := derived28 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c35 : DefaultClause 29 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f35 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c34, some c14, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p35 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked35 : lratChecker f35 p35 = .success := by decide +kernel
theorem unsat35 : Unsatisfiable (PosFin 29) f35 := by
  apply lratCheckerSound f35 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p35
  · intro a ha; simp [p35] at ha; subst a; trivial
  · exact checked35
theorem derived35 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c35 := by
  apply localUnsat_implies_entails f35 [c34, c14] c35 unsat35 (by rfl) a
  have h0 : Entails.eval a c34 := derived34 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c36 : DefaultClause 29 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f36 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c34, some c29, some c32, some c20, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p36 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked36 : lratChecker f36 p36 = .success := by decide +kernel
theorem unsat36 : Unsatisfiable (PosFin 29) f36 := by
  apply lratCheckerSound f36 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p36
  · intro a ha; simp [p36] at ha; subst a; trivial
  · exact checked36
theorem derived36 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c36 := by
  apply localUnsat_implies_entails f36 [c34, c29, c32, c20] c36 unsat36 (by rfl) a
  have h0 : Entails.eval a c34 := derived34 a h
  have h1 : Entails.eval a c29 := derived29 a h
  have h2 : Entails.eval a c32 := derived32 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c37 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f37 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c35, some c36, some c10]
def p37 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked37 : lratChecker f37 p37 = .success := by decide +kernel
theorem unsat37 : Unsatisfiable (PosFin 29) f37 := by
  apply lratCheckerSound f37 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p37
  · intro a ha; simp [p37] at ha; subst a; trivial
  · exact checked37
theorem derived37 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c37 := by
  apply localUnsat_implies_entails f37 [c35, c36, c10] c37 unsat37 (by rfl) a
  have h0 : Entails.eval a c35 := derived35 a h
  have h1 : Entails.eval a c36 := derived36 a h
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived37

end CochromaticTwenty.Certificates.Z12Direct_4_3_6
