import MerLeanExperiment.Certificates.Z12Direct_4_5_6.Inputs

/-! Generated from the actual pinned z12direct_4_5_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c27 : DefaultClause 29 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f27 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c11, some c6, some c4, some c9, some c2, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p27 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked27 : lratChecker f27 p27 = .success := by decide +kernel
theorem unsat27 : Unsatisfiable (PosFin 29) f27 := by
  apply lratCheckerSound f27 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p27
  · intro a ha; simp [p27] at ha; subst a; trivial
  · exact checked27
theorem derived27 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c27 := by
  apply localUnsat_implies_entails f27 [c11, c6, c4, c9, c2] c27 unsat27 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c28 : DefaultClause 29 := directClause [(⟨5, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f28 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c11, some c6, some c14, some c18, some c2, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p28 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked28 : lratChecker f28 p28 = .success := by decide +kernel
theorem unsat28 : Unsatisfiable (PosFin 29) f28 := by
  apply lratCheckerSound f28 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p28
  · intro a ha; simp [p28] at ha; subst a; trivial
  · exact checked28
theorem derived28 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c28 := by
  apply localUnsat_implies_entails f28 [c11, c6, c14, c18, c2] c28 unsat28 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c29 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f29 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c15, some c5, some c13, some c17, some c26, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p29 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked29 : lratChecker f29 p29 = .success := by decide +kernel
theorem unsat29 : Unsatisfiable (PosFin 29) f29 := by
  apply lratCheckerSound f29 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p29
  · intro a ha; simp [p29] at ha; subst a; trivial
  · exact checked29
theorem derived29 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c29 := by
  apply localUnsat_implies_entails f29 [c15, c5, c13, c17, c26] c29 unsat29 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c30 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f30 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c11, some c6, some c5, some c15, some c29, some c23, some c3, some c8, some c26, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p30 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked30 : lratChecker f30 p30 = .success := by decide +kernel
theorem unsat30 : Unsatisfiable (PosFin 29) f30 := by
  apply lratCheckerSound f30 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p30
  · intro a ha; simp [p30] at ha; subst a; trivial
  · exact checked30
theorem derived30 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c30 := by
  apply localUnsat_implies_entails f30 [c11, c6, c5, c15, c29, c23, c3, c8, c26] c30 unsat30 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c29 := derived29 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c31 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f31 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c19, some c10, some c3, some c8, some c26, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p31 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked31 : lratChecker f31 p31 = .success := by decide +kernel
theorem unsat31 : Unsatisfiable (PosFin 29) f31 := by
  apply lratCheckerSound f31 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p31
  · intro a ha; simp [p31] at ha; subst a; trivial
  · exact checked31
theorem derived31 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c31 := by
  apply localUnsat_implies_entails f31 [c19, c10, c3, c8, c26] c31 unsat31 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c32 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f32 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c6, some c11, some c27, some c28, some c30, some c21, some c10, some c19, some c31, some c23, some c13, some c17, some c26, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p32 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked32 : lratChecker f32 p32 = .success := by decide +kernel
theorem unsat32 : Unsatisfiable (PosFin 29) f32 := by
  apply lratCheckerSound f32 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p32
  · intro a ha; simp [p32] at ha; subst a; trivial
  · exact checked32
theorem derived32 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c32 := by
  apply localUnsat_implies_entails f32 [c6, c11, c27, c28, c30, c21, c10, c19, c31, c23, c13, c17, c26] c32 unsat32 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c27 := derived27 a h
  have h3 : Entails.eval a c28 := derived28 a h
  have h4 : Entails.eval a c30 := derived30 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c31 := derived31 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c33 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f33 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c16, some c20, some c23, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p33 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked33 : lratChecker f33 p33 = .success := by decide +kernel
theorem unsat33 : Unsatisfiable (PosFin 29) f33 := by
  apply lratCheckerSound f33 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p33
  · intro a ha; simp [p33] at ha; subst a; trivial
  · exact checked33
theorem derived33 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c33 := by
  apply localUnsat_implies_entails f33 [c16, c20, c23] c33 unsat33 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c34 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f34 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c10, some c12, some c19, some c31, some c26, some c13, some c33, some c1, some c14, some c18, some c22, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p34 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked34 : lratChecker f34 p34 = .success := by decide +kernel
theorem unsat34 : Unsatisfiable (PosFin 29) f34 := by
  apply lratCheckerSound f34 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p34
  · intro a ha; simp [p34] at ha; subst a; trivial
  · exact checked34
theorem derived34 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c34 := by
  apply localUnsat_implies_entails f34 [c32, c10, c12, c19, c31, c26, c13, c33, c1, c14, c18, c22] c34 unsat34 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c31 := derived31 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c33 := derived33 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c35 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f35 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c18, some c14, some c16, some c20, some c2, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p35 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked35 : lratChecker f35 p35 = .success := by decide +kernel
theorem unsat35 : Unsatisfiable (PosFin 29) f35 := by
  apply lratCheckerSound f35 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p35
  · intro a ha; simp [p35] at ha; subst a; trivial
  · exact checked35
theorem derived35 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c35 := by
  apply localUnsat_implies_entails f35 [c18, c14, c16, c20, c2] c35 unsat35 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c36 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f36 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c8, some c17, some c25, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p36 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked36 : lratChecker f36 p36 = .success := by decide +kernel
theorem unsat36 : Unsatisfiable (PosFin 29) f36 := by
  apply lratCheckerSound f36 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p36
  · intro a ha; simp [p36] at ha; subst a; trivial
  · exact checked36
theorem derived36 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c36 := by
  apply localUnsat_implies_entails f36 [c8, c17, c25] c36 unsat36 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c37 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f37 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c21, some c35, some c36, some c24, some c3, some c13, some c25, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p37 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked37 : lratChecker f37 p37 = .success := by decide +kernel
theorem unsat37 : Unsatisfiable (PosFin 29) f37 := by
  apply lratCheckerSound f37 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p37
  · intro a ha; simp [p37] at ha; subst a; trivial
  · exact checked37
theorem derived37 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c37 := by
  apply localUnsat_implies_entails f37 [c32, c21, c35, c36, c24, c3, c13, c25] c37 unsat37 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c35 := derived35 a h
  have h3 : Entails.eval a c36 := derived36 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c38 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f38 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c37, some c5, some c7, some c15, some c29, some c26, some c8, some c33, some c1, some c14, some c18, some c22, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p38 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked38 : lratChecker f38 p38 = .success := by decide +kernel
theorem unsat38 : Unsatisfiable (PosFin 29) f38 := by
  apply lratCheckerSound f38 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p38
  · intro a ha; simp [p38] at ha; subst a; trivial
  · exact checked38
theorem derived38 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c38 := by
  apply localUnsat_implies_entails f38 [c32, c37, c5, c7, c15, c29, c26, c8, c33, c1, c14, c18, c22] c38 unsat38 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c37 := derived37 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c29 := derived29 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c33 := derived33 a h
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c39 : DefaultClause 29 := directClause [(⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f39 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c34, some c38, some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p39 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked39 : lratChecker f39 p39 = .success := by decide +kernel
theorem unsat39 : Unsatisfiable (PosFin 29) f39 := by
  apply lratCheckerSound f39 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p39
  · intro a ha; simp [p39] at ha; subst a; trivial
  · exact checked39
theorem derived39 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c39 := by
  apply localUnsat_implies_entails f39 [c34, c38] c39 unsat39 (by rfl) a
  have h0 : Entails.eval a c34 := derived34 a h
  have h1 : Entails.eval a c38 := derived38 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c40 : DefaultClause 29 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f40 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c39, some c4, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p40 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked40 : lratChecker f40 p40 = .success := by decide +kernel
theorem unsat40 : Unsatisfiable (PosFin 29) f40 := by
  apply lratCheckerSound f40 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p40
  · intro a ha; simp [p40] at ha; subst a; trivial
  · exact checked40
theorem derived40 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c40 := by
  apply localUnsat_implies_entails f40 [c39, c4] c40 unsat40 (by rfl) a
  have h0 : Entails.eval a c39 := derived39 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c41 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f41 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c39, some c9, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p41 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked41 : lratChecker f41 p41 = .success := by decide +kernel
theorem unsat41 : Unsatisfiable (PosFin 29) f41 := by
  apply lratCheckerSound f41 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p41
  · intro a ha; simp [p41] at ha; subst a; trivial
  · exact checked41
theorem derived41 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c41 := by
  apply localUnsat_implies_entails f41 [c39, c9] c41 unsat41 (by rfl) a
  have h0 : Entails.eval a c39 := derived39 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c42 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f42 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c41, some c40, some c5, some c15, some c22, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p42 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked42 : lratChecker f42 p42 = .success := by decide +kernel
theorem unsat42 : Unsatisfiable (PosFin 29) f42 := by
  apply lratCheckerSound f42 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p42
  · intro a ha; simp [p42] at ha; subst a; trivial
  · exact checked42
theorem derived42 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c42 := by
  apply localUnsat_implies_entails f42 [c41, c40, c5, c15, c22] c42 unsat42 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c40 := derived40 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c15 := h 14 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c43 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f43 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c41, some c40, some c16, some c20, some c2, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p43 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked43 : lratChecker f43 p43 = .success := by decide +kernel
theorem unsat43 : Unsatisfiable (PosFin 29) f43 := by
  apply lratCheckerSound f43 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p43
  · intro a ha; simp [p43] at ha; subst a; trivial
  · exact checked43
theorem derived43 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c43 := by
  apply localUnsat_implies_entails f43 [c41, c40, c16, c20, c2] c43 unsat43 (by rfl) a
  have h0 : Entails.eval a c41 := derived41 a h
  have h1 : Entails.eval a c40 := derived40 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c44 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f44 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c43, some c42, some c36, some c24, some c3, some c13, some c25, some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p44 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked44 : lratChecker f44 p44 = .success := by decide +kernel
theorem unsat44 : Unsatisfiable (PosFin 29) f44 := by
  apply lratCheckerSound f44 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p44
  · intro a ha; simp [p44] at ha; subst a; trivial
  · exact checked44
theorem derived44 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c44 := by
  apply localUnsat_implies_entails f44 [c32, c43, c42, c36, c24, c3, c13, c25] c44 unsat44 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c43 := derived43 a h
  have h2 : Entails.eval a c42 := derived42 a h
  have h3 : Entails.eval a c36 := derived36 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c45 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f45 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c44, some c10, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p45 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked45 : lratChecker f45 p45 = .success := by decide +kernel
theorem unsat45 : Unsatisfiable (PosFin 29) f45 := by
  apply lratCheckerSound f45 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p45
  · intro a ha; simp [p45] at ha; subst a; trivial
  · exact checked45
theorem derived45 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c45 := by
  apply localUnsat_implies_entails f45 [c44, c10] c45 unsat45 (by rfl) a
  have h0 : Entails.eval a c44 := derived44 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c46 : DefaultClause 29 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f46 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c44, some c19, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p46 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked46 : lratChecker f46 p46 = .success := by decide +kernel
theorem unsat46 : Unsatisfiable (PosFin 29) f46 := by
  apply lratCheckerSound f46 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p46
  · intro a ha; simp [p46] at ha; subst a; trivial
  · exact checked46
theorem derived46 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c46 := by
  apply localUnsat_implies_entails f46 [c44, c19] c46 unsat46 (by rfl) a
  have h0 : Entails.eval a c44 := derived44 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c47 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f47 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c46, some c45, some c40, some c41, some c22]
def p47 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked47 : lratChecker f47 p47 = .success := by decide +kernel
theorem unsat47 : Unsatisfiable (PosFin 29) f47 := by
  apply lratCheckerSound f47 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p47
  · intro a ha; simp [p47] at ha; subst a; trivial
  · exact checked47
theorem derived47 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c47 := by
  apply localUnsat_implies_entails f47 [c46, c45, c40, c41, c22] c47 unsat47 (by rfl) a
  have h0 : Entails.eval a c46 := derived46 a h
  have h1 : Entails.eval a c45 := derived45 a h
  have h2 : Entails.eval a c40 := derived40 a h
  have h3 : Entails.eval a c41 := derived41 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived47

end CochromaticTwenty.Certificates.Z12Direct_4_5_6
