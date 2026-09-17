import MerLeanExperiment.Certificates.Z12Direct_4_2_6.Inputs

/-! Generated from the actual pinned z12direct_4_2_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_2_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c23 : DefaultClause 22 := directClause [(⟨7, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f23 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c12, some c5, some c1, some c10, some c17, some c16, some c22, some c11, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p23 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked23 : lratChecker f23 p23 = .success := by decide +kernel
theorem unsat23 : Unsatisfiable (PosFin 22) f23 := by
  apply lratCheckerSound f23 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p23
  · intro a ha; simp [p23] at ha; subst a; trivial
  · exact checked23
theorem derived23 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c23 := by
  apply localUnsat_implies_entails f23 [c12, c5, c1, c10, c17, c16, c22, c11] c23 unsat23 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c24 : DefaultClause 22 := directClause [(⟨14, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f24 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c2, some c4, some c17, some c9, some c21, some c11, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p24 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked24 : lratChecker f24 p24 = .success := by decide +kernel
theorem unsat24 : Unsatisfiable (PosFin 22) f24 := by
  apply lratCheckerSound f24 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p24
  · intro a ha; simp [p24] at ha; subst a; trivial
  · exact checked24
theorem derived24 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c24 := by
  apply localUnsat_implies_entails f24 [c2, c4, c17, c9, c21, c11] c24 unsat24 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c25 : DefaultClause 22 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f25 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c5, some c23, some c20, some c24, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p25 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked25 : lratChecker f25 p25 = .success := by decide +kernel
theorem unsat25 : Unsatisfiable (PosFin 22) f25 := by
  apply lratCheckerSound f25 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p25
  · intro a ha; simp [p25] at ha; subst a; trivial
  · exact checked25
theorem derived25 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c25 := by
  apply localUnsat_implies_entails f25 [c5, c23, c20, c24] c25 unsat25 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c23 := derived23 a h
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c24 := derived24 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c26 : DefaultClause 22 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f26 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c25, some c3, some c4, some c10, some c7, some c14, some c18, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p26 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked26 : lratChecker f26 p26 = .success := by decide +kernel
theorem unsat26 : Unsatisfiable (PosFin 22) f26 := by
  apply lratCheckerSound f26 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p26
  · intro a ha; simp [p26] at ha; subst a; trivial
  · exact checked26
theorem derived26 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c26 := by
  apply localUnsat_implies_entails f26 [c25, c3, c4, c10, c7, c14, c18] c26 unsat26 (by rfl) a
  have h0 : Entails.eval a c25 := derived25 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c27 : DefaultClause 22 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f27 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c26, some c6, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p27 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2]]
theorem checked27 : lratChecker f27 p27 = .success := by decide +kernel
theorem unsat27 : Unsatisfiable (PosFin 22) f27 := by
  apply lratCheckerSound f27 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p27
  · intro a ha; simp [p27] at ha; subst a; trivial
  · exact checked27
theorem derived27 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c27 := by
  apply localUnsat_implies_entails f27 [c26, c6] c27 unsat27 (by rfl) a
  have h0 : Entails.eval a c26 := derived26 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c28 : DefaultClause 22 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f28 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c26, some c13, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p28 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2]]
theorem checked28 : lratChecker f28 p28 = .success := by decide +kernel
theorem unsat28 : Unsatisfiable (PosFin 22) f28 := by
  apply lratCheckerSound f28 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p28
  · intro a ha; simp [p28] at ha; subst a; trivial
  · exact checked28
theorem derived28 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c28 := by
  apply localUnsat_implies_entails f28 [c26, c13] c28 unsat28 (by rfl) a
  have h0 : Entails.eval a c26 := derived26 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c29 : DefaultClause 22 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f29 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c27, some c24, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p29 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2]]
theorem checked29 : lratChecker f29 p29 = .success := by decide +kernel
theorem unsat29 : Unsatisfiable (PosFin 22) f29 := by
  apply lratCheckerSound f29 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p29
  · intro a ha; simp [p29] at ha; subst a; trivial
  · exact checked29
theorem derived29 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c29 := by
  apply localUnsat_implies_entails f29 [c27, c24] c29 unsat29 (by rfl) a
  have h0 : Entails.eval a c27 := derived27 a h
  have h1 : Entails.eval a c24 := derived24 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c30 : DefaultClause 22 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f30 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c29, some c19, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p30 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2]]
theorem checked30 : lratChecker f30 p30 = .success := by decide +kernel
theorem unsat30 : Unsatisfiable (PosFin 22) f30 := by
  apply lratCheckerSound f30 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p30
  · intro a ha; simp [p30] at ha; subst a; trivial
  · exact checked30
theorem derived30 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c30 := by
  apply localUnsat_implies_entails f30 [c29, c19] c30 unsat30 (by rfl) a
  have h0 : Entails.eval a c29 := derived29 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c31 : DefaultClause 22 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f31 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c30, some c28, some c1, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p31 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked31 : lratChecker f31 p31 = .success := by decide +kernel
theorem unsat31 : Unsatisfiable (PosFin 22) f31 := by
  apply lratCheckerSound f31 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p31
  · intro a ha; simp [p31] at ha; subst a; trivial
  · exact checked31
theorem derived31 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c31 := by
  apply localUnsat_implies_entails f31 [c30, c28, c1] c31 unsat31 (by rfl) a
  have h0 : Entails.eval a c30 := derived30 a h
  have h1 : Entails.eval a c28 := derived28 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c32 : DefaultClause 22 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f32 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c31, some c10, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p32 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2]]
theorem checked32 : lratChecker f32 p32 = .success := by decide +kernel
theorem unsat32 : Unsatisfiable (PosFin 22) f32 := by
  apply lratCheckerSound f32 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p32
  · intro a ha; simp [p32] at ha; subst a; trivial
  · exact checked32
theorem derived32 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c32 := by
  apply localUnsat_implies_entails f32 [c31, c10] c32 unsat32 (by rfl) a
  have h0 : Entails.eval a c31 := derived31 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c33 : DefaultClause 22 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f33 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c32, some c27, some c25, some c8, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p33 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked33 : lratChecker f33 p33 = .success := by decide +kernel
theorem unsat33 : Unsatisfiable (PosFin 22) f33 := by
  apply lratCheckerSound f33 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p33
  · intro a ha; simp [p33] at ha; subst a; trivial
  · exact checked33
theorem derived33 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c33 := by
  apply localUnsat_implies_entails f33 [c32, c27, c25, c8] c33 unsat33 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c27 := derived27 a h
  have h2 : Entails.eval a c25 := derived25 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c34 : DefaultClause 22 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f34 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c32, some c28, some c25, some c15, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p34 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked34 : lratChecker f34 p34 = .success := by decide +kernel
theorem unsat34 : Unsatisfiable (PosFin 22) f34 := by
  apply lratCheckerSound f34 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p34
  · intro a ha; simp [p34] at ha; subst a; trivial
  · exact checked34
theorem derived34 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c34 := by
  apply localUnsat_implies_entails f34 [c32, c28, c25, c15] c34 unsat34 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c28 := derived28 a h
  have h2 : Entails.eval a c25 := derived25 a h
  have h3 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c35 : DefaultClause 22 := directClause [] (by decide +kernel) (by decide +kernel)
def f35 : DefaultFormula 22 := DefaultFormula.ofArray #[none, some c34, some c33, some c18]
def p35 : List (Action (DefaultClause 22) (PosFin 22)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked35 : lratChecker f35 p35 = .success := by decide +kernel
theorem unsat35 : Unsatisfiable (PosFin 22) f35 := by
  apply lratCheckerSound f35 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p35
  · intro a ha; simp [p35] at ha; subst a; trivial
  · exact checked35
theorem derived35 (a : PosFin 22 → Bool) (h : InputSat a) : Entails.eval a c35 := by
  apply localUnsat_implies_entails f35 [c34, c33, c18] c35 unsat35 (by rfl) a
  have h0 : Entails.eval a c34 := derived34 a h
  have h1 : Entails.eval a c33 := derived33 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived35

end CochromaticTwenty.Certificates.Z12Direct_4_2_6
