import MerLeanExperiment.Certificates.Z12Direct_4_5_7.Inputs

/-! Generated from the actual pinned z12direct_4_5_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_5_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c19 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f19 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c8, some c5, some c4, some c7, some c2, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p19 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked19 : lratChecker f19 p19 = .success := by decide +kernel
theorem unsat19 : Unsatisfiable (PosFin 29) f19 := by
  apply lratCheckerSound f19 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p19
  · intro a ha; simp [p19] at ha; subst a; trivial
  · exact checked19
theorem derived19 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c19 := by
  apply localUnsat_implies_entails f19 [c8, c5, c4, c7, c2] c19 unsat19 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c4 := h 3 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c20 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f20 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c9, some c12, some c18, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p20 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked20 : lratChecker f20 p20 = .success := by decide +kernel
theorem unsat20 : Unsatisfiable (PosFin 29) f20 := by
  apply lratCheckerSound f20 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p20
  · intro a ha; simp [p20] at ha; subst a; trivial
  · exact checked20
theorem derived20 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c20 := by
  apply localUnsat_implies_entails f20 [c9, c12, c18] c20 unsat20 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c21 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f21 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c19, some c8, some c5, some c20, some c15, some c3, some c6, some c18, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p21 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked21 : lratChecker f21 p21 = .success := by decide +kernel
theorem unsat21 : Unsatisfiable (PosFin 29) f21 := by
  apply lratCheckerSound f21 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p21
  · intro a ha; simp [p21] at ha; subst a; trivial
  · exact checked21
theorem derived21 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c21 := by
  apply localUnsat_implies_entails f21 [c19, c8, c5, c20, c15, c3, c6, c18] c21 unsat21 (by rfl) a
  have h0 : Entails.eval a c19 := derived19 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c20 := derived20 a h
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c22 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f22 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c5, some c8, some c21, some c10, some c13, some c2, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p22 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked22 : lratChecker f22 p22 = .success := by decide +kernel
theorem unsat22 : Unsatisfiable (PosFin 29) f22 := by
  apply lratCheckerSound f22 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p22
  · intro a ha; simp [p22] at ha; subst a; trivial
  · exact checked22
theorem derived22 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c22 := by
  apply localUnsat_implies_entails f22 [c5, c8, c21, c10, c13, c2] c22 unsat22 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c21 := derived21 a h
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c23 : DefaultClause 29 := directClause [(⟨6, by decide⟩, true), (⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f23 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c20, some c15, some c3, some c6, some c18, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p23 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked23 : lratChecker f23 p23 = .success := by decide +kernel
theorem unsat23 : Unsatisfiable (PosFin 29) f23 := by
  apply lratCheckerSound f23 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p23
  · intro a ha; simp [p23] at ha; subst a; trivial
  · exact checked23
theorem derived23 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c23 := by
  apply localUnsat_implies_entails f23 [c20, c15, c3, c6, c18] c23 unsat23 (by rfl) a
  have h0 : Entails.eval a c20 := derived20 a h
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c24 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f24 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c23, some c10, some c13, some c2, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p24 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked24 : lratChecker f24 p24 = .success := by decide +kernel
theorem unsat24 : Unsatisfiable (PosFin 29) f24 := by
  apply lratCheckerSound f24 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p24
  · intro a ha; simp [p24] at ha; subst a; trivial
  · exact checked24
theorem derived24 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c24 := by
  apply localUnsat_implies_entails f24 [c23, c10, c13, c2] c24 unsat24 (by rfl) a
  have h0 : Entails.eval a c23 := derived23 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c25 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f25 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c22, some c3, some c6, some c16, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p25 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked25 : lratChecker f25 p25 = .success := by decide +kernel
theorem unsat25 : Unsatisfiable (PosFin 29) f25 := by
  apply lratCheckerSound f25 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p25
  · intro a ha; simp [p25] at ha; subst a; trivial
  · exact checked25
theorem derived25 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c25 := by
  apply localUnsat_implies_entails f25 [c22, c3, c6, c16] c25 unsat25 (by rfl) a
  have h0 : Entails.eval a c22 := derived22 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c26 : DefaultClause 29 := directClause [(⟨7, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f26 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c22, some c1, some c10, some c13, some c25, some c17, some c9, some c12, some c16, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p26 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked26 : lratChecker f26 p26 = .success := by decide +kernel
theorem unsat26 : Unsatisfiable (PosFin 29) f26 := by
  apply lratCheckerSound f26 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p26
  · intro a ha; simp [p26] at ha; subst a; trivial
  · exact checked26
theorem derived26 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c26 := by
  apply localUnsat_implies_entails f26 [c22, c1, c10, c13, c25, c17, c9, c12, c16] c26 unsat26 (by rfl) a
  have h0 : Entails.eval a c22 := derived22 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c25 := derived25 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c27 : DefaultClause 29 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f27 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c26, some c11, some c14, some c24, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p27 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked27 : lratChecker f27 p27 = .success := by decide +kernel
theorem unsat27 : Unsatisfiable (PosFin 29) f27 := by
  apply lratCheckerSound f27 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p27
  · intro a ha; simp [p27] at ha; subst a; trivial
  · exact checked27
theorem derived27 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c27 := by
  apply localUnsat_implies_entails f27 [c26, c11, c14, c24] c27 unsat27 (by rfl) a
  have h0 : Entails.eval a c26 := derived26 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c24 := derived24 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c28 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f28 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c27, some c4, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p28 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked28 : lratChecker f28 p28 = .success := by decide +kernel
theorem unsat28 : Unsatisfiable (PosFin 29) f28 := by
  apply lratCheckerSound f28 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p28
  · intro a ha; simp [p28] at ha; subst a; trivial
  · exact checked28
theorem derived28 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c28 := by
  apply localUnsat_implies_entails f28 [c27, c4] c28 unsat28 (by rfl) a
  have h0 : Entails.eval a c27 := derived27 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c29 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f29 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c27, some c7, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p29 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked29 : lratChecker f29 p29 = .success := by decide +kernel
theorem unsat29 : Unsatisfiable (PosFin 29) f29 := by
  apply lratCheckerSound f29 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p29
  · intro a ha; simp [p29] at ha; subst a; trivial
  · exact checked29
theorem derived29 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c29 := by
  apply localUnsat_implies_entails f29 [c27, c7] c29 unsat29 (by rfl) a
  have h0 : Entails.eval a c27 := derived27 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c30 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f30 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c29, some c28, some c11, some c14, some c2, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p30 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked30 : lratChecker f30 p30 = .success := by decide +kernel
theorem unsat30 : Unsatisfiable (PosFin 29) f30 := by
  apply lratCheckerSound f30 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p30
  · intro a ha; simp [p30] at ha; subst a; trivial
  · exact checked30
theorem derived30 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c30 := by
  apply localUnsat_implies_entails f30 [c29, c28, c11, c14, c2] c30 unsat30 (by rfl) a
  have h0 : Entails.eval a c29 := derived29 a h
  have h1 : Entails.eval a c28 := derived28 a h
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c31 : DefaultClause 29 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f31 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c30, some c25, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p31 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked31 : lratChecker f31 p31 = .success := by decide +kernel
theorem unsat31 : Unsatisfiable (PosFin 29) f31 := by
  apply lratCheckerSound f31 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p31
  · intro a ha; simp [p31] at ha; subst a; trivial
  · exact checked31
theorem derived31 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c31 := by
  apply localUnsat_implies_entails f31 [c30, c25] c31 unsat31 (by rfl) a
  have h0 : Entails.eval a c30 := derived30 a h
  have h1 : Entails.eval a c25 := derived25 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c32 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f32 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c31, some c29, some c28, some c17, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p32 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked32 : lratChecker f32 p32 = .success := by decide +kernel
theorem unsat32 : Unsatisfiable (PosFin 29) f32 := by
  apply lratCheckerSound f32 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p32
  · intro a ha; simp [p32] at ha; subst a; trivial
  · exact checked32
theorem derived32 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c32 := by
  apply localUnsat_implies_entails f32 [c31, c29, c28, c17] c32 unsat32 (by rfl) a
  have h0 : Entails.eval a c31 := derived31 a h
  have h1 : Entails.eval a c29 := derived29 a h
  have h2 : Entails.eval a c28 := derived28 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c33 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f33 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c9, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p33 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked33 : lratChecker f33 p33 = .success := by decide +kernel
theorem unsat33 : Unsatisfiable (PosFin 29) f33 := by
  apply lratCheckerSound f33 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p33
  · intro a ha; simp [p33] at ha; subst a; trivial
  · exact checked33
theorem derived33 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c33 := by
  apply localUnsat_implies_entails f33 [c32, c9] c33 unsat33 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c34 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f34 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c32, some c12, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p34 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked34 : lratChecker f34 p34 = .success := by decide +kernel
theorem unsat34 : Unsatisfiable (PosFin 29) f34 := by
  apply lratCheckerSound f34 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p34
  · intro a ha; simp [p34] at ha; subst a; trivial
  · exact checked34
theorem derived34 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c34 := by
  apply localUnsat_implies_entails f34 [c32, c12] c34 unsat34 (by rfl) a
  have h0 : Entails.eval a c32 := derived32 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c35 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f35 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c34, some c33, some c30, some c22, some c16]
def p35 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked35 : lratChecker f35 p35 = .success := by decide +kernel
theorem unsat35 : Unsatisfiable (PosFin 29) f35 := by
  apply lratCheckerSound f35 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p35
  · intro a ha; simp [p35] at ha; subst a; trivial
  · exact checked35
theorem derived35 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c35 := by
  apply localUnsat_implies_entails f35 [c34, c33, c30, c22, c16] c35 unsat35 (by rfl) a
  have h0 : Entails.eval a c34 := derived34 a h
  have h1 : Entails.eval a c33 := derived33 a h
  have h2 : Entails.eval a c30 := derived30 a h
  have h3 : Entails.eval a c22 := derived22 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived35

end CochromaticTwenty.Certificates.Z12Direct_4_5_7
