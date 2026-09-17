import MerLeanExperiment.Certificates.B16_3_2.Steps0300_0399

/-! Generated from the actual pinned b16_3_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c799 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f799 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c778, some c791, some c796, some c384, some c133, some c388, some c184, some c766, some c782, some c507, some c717, some c174, some c186, some c347, some c798, some c278, some c24, some c328, some c329, some c130, some c22, some c294, some c7, some c350, some c57, some c72, some c318, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p799 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked799 : lratChecker f799 p799 = .success := by decide +kernel
theorem unsat799 : Unsatisfiable (PosFin 57) f799 := by
  apply lratCheckerSound f799 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p799
  · intro a ha; simp [p799] at ha; subst a; trivial
  · exact checked799
theorem derived799 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c799 := by
  apply localUnsat_implies_entails f799 [c778, c791, c796, c384, c133, c388, c184, c766, c782, c507, c717, c174, c186, c347, c798, c278, c24, c328, c329, c130, c22, c294, c7, c350, c57, c72, c318] c799 unsat799 (by rfl) a
  have h0 : Entails.eval a c778 := derived778 a h
  have h1 : Entails.eval a c791 := derived791 a h
  have h2 : Entails.eval a c796 := derived796 a h
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c184 := h 183 (by decide)
  have h7 : Entails.eval a c766 := derived766 a h
  have h8 : Entails.eval a c782 := derived782 a h
  have h9 : Entails.eval a c507 := derived507 a h
  have h10 : Entails.eval a c717 := derived717 a h
  have h11 : Entails.eval a c174 := h 173 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c798 := derived798 a h
  have h15 : Entails.eval a c278 := h 277 (by decide)
  have h16 : Entails.eval a c24 := h 23 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c329 := h 328 (by decide)
  have h19 : Entails.eval a c130 := h 129 (by decide)
  have h20 : Entails.eval a c22 := h 21 (by decide)
  have h21 : Entails.eval a c294 := h 293 (by decide)
  have h22 : Entails.eval a c7 := h 6 (by decide)
  have h23 : Entails.eval a c350 := h 349 (by decide)
  have h24 : Entails.eval a c57 := h 56 (by decide)
  have h25 : Entails.eval a c72 := h 71 (by decide)
  have h26 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c800 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f800 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c759, some c778, some c791, some c796, some c388, some c384, some c133, some c799, some c117, some c124, some c65, some c776, some c93, some c111, some c94, some c74, some c72, some c390, some c345, some c349, some c779, some c159, some c294, some c14, some c312, some c137, some c70, some c260, some c121, some c374, some c113, some c394, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p800 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked800 : lratChecker f800 p800 = .success := by decide +kernel
theorem unsat800 : Unsatisfiable (PosFin 57) f800 := by
  apply lratCheckerSound f800 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p800
  · intro a ha; simp [p800] at ha; subst a; trivial
  · exact checked800
theorem derived800 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c800 := by
  apply localUnsat_implies_entails f800 [c766, c759, c778, c791, c796, c388, c384, c133, c799, c117, c124, c65, c776, c93, c111, c94, c74, c72, c390, c345, c349, c779, c159, c294, c14, c312, c137, c70, c260, c121, c374, c113, c394] c800 unsat800 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c791 := derived791 a h
  have h4 : Entails.eval a c796 := derived796 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c799 := derived799 a h
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c776 := derived776 a h
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c111 := h 110 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c390 := h 389 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  have h21 : Entails.eval a c779 := derived779 a h
  have h22 : Entails.eval a c159 := h 158 (by decide)
  have h23 : Entails.eval a c294 := h 293 (by decide)
  have h24 : Entails.eval a c14 := h 13 (by decide)
  have h25 : Entails.eval a c312 := h 311 (by decide)
  have h26 : Entails.eval a c137 := h 136 (by decide)
  have h27 : Entails.eval a c70 := h 69 (by decide)
  have h28 : Entails.eval a c260 := h 259 (by decide)
  have h29 : Entails.eval a c121 := h 120 (by decide)
  have h30 : Entails.eval a c374 := h 373 (by decide)
  have h31 : Entails.eval a c113 := h 112 (by decide)
  have h32 : Entails.eval a c394 := h 393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c801 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, true), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f801 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c52, some c24, some c296, some c133, some c278, some c139, some c31, some c14, some c117, some c124, some c65, some c776, some c74, some c312, some c92, some c388, some c349, some c184, some c93, some c70, some c7, some c121, some c181, some c75, some c369, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p801 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked801 : lratChecker f801 p801 = .success := by decide +kernel
theorem unsat801 : Unsatisfiable (PosFin 57) f801 := by
  apply lratCheckerSound f801 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p801
  · intro a ha; simp [p801] at ha; subst a; trivial
  · exact checked801
theorem derived801 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c801 := by
  apply localUnsat_implies_entails f801 [c328, c52, c24, c296, c133, c278, c139, c31, c14, c117, c124, c65, c776, c74, c312, c92, c388, c349, c184, c93, c70, c7, c121, c181, c75, c369] c801 unsat801 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c296 := h 295 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c776 := derived776 a h
  have h13 : Entails.eval a c74 := h 73 (by decide)
  have h14 : Entails.eval a c312 := h 311 (by decide)
  have h15 : Entails.eval a c92 := h 91 (by decide)
  have h16 : Entails.eval a c388 := h 387 (by decide)
  have h17 : Entails.eval a c349 := h 348 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c93 := h 92 (by decide)
  have h20 : Entails.eval a c70 := h 69 (by decide)
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c121 := h 120 (by decide)
  have h23 : Entails.eval a c181 := h 180 (by decide)
  have h24 : Entails.eval a c75 := h 74 (by decide)
  have h25 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c802 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨38, by decide⟩, true), (⟨42, by decide⟩, true), (⟨41, by decide⟩, true), (⟨30, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f802 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c124, some c65, some c93, some c94, some c74, some c312, some c70, some c121, some c95, some c75, some c343, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p802 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked802 : lratChecker f802 p802 = .success := by decide +kernel
theorem unsat802 : Unsatisfiable (PosFin 57) f802 := by
  apply lratCheckerSound f802 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p802
  · intro a ha; simp [p802] at ha; subst a; trivial
  · exact checked802
theorem derived802 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c802 := by
  apply localUnsat_implies_entails f802 [c117, c124, c65, c93, c94, c74, c312, c70, c121, c95, c75, c343] c802 unsat802 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c803 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨31, by decide⟩, true), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f803 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c800, some c766, some c759, some c328, some c296, some c24, some c52, some c801, some c768, some c92, some c388, some c349, some c802, some c51, some c764, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p803 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked803 : lratChecker f803 p803 = .success := by decide +kernel
theorem unsat803 : Unsatisfiable (PosFin 57) f803 := by
  apply lratCheckerSound f803 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p803
  · intro a ha; simp [p803] at ha; subst a; trivial
  · exact checked803
theorem derived803 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c803 := by
  apply localUnsat_implies_entails f803 [c800, c766, c759, c328, c296, c24, c52, c801, c768, c92, c388, c349, c802, c51, c764] c803 unsat803 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c759 := derived759 a h
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c801 := derived801 a h
  have h8 : Entails.eval a c768 := derived768 a h
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c802 := derived802 a h
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c764 := derived764 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c804 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨30, by decide⟩, true), (⟨46, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f804 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c130, some c800, some c91, some c659, some c92, some c388, some c384, some c97, some c7, some c184, some c188, some c757, some c198, some c65, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p804 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked804 : lratChecker f804 p804 = .success := by decide +kernel
theorem unsat804 : Unsatisfiable (PosFin 57) f804 := by
  apply lratCheckerSound f804 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p804
  · intro a ha; simp [p804] at ha; subst a; trivial
  · exact checked804
theorem derived804 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c804 := by
  apply localUnsat_implies_entails f804 [c22, c130, c800, c91, c659, c92, c388, c384, c97, c7, c184, c188, c757, c198, c65] c804 unsat804 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c130 := h 129 (by decide)
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c757 := derived757 a h
  have h13 : Entails.eval a c198 := h 197 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c805 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f805 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c34, some c278, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p805 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked805 : lratChecker f805 p805 = .success := by decide +kernel
theorem unsat805 : Unsatisfiable (PosFin 57) f805 := by
  apply lratCheckerSound f805 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p805
  · intro a ha; simp [p805] at ha; subst a; trivial
  · exact checked805
theorem derived805 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c805 := by
  apply localUnsat_implies_entails f805 [c39, c34, c278] c805 unsat805 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c806 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨31, by decide⟩, true), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f806 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c759, some c803, some c231, some c804, some c117, some c124, some c74, some c805, some c283, some c242, some c229, some c159, some c294, some c14, some c137, some c295, some c776, some c72, some c92, some c349, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p806 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked806 : lratChecker f806 p806 = .success := by decide +kernel
theorem unsat806 : Unsatisfiable (PosFin 57) f806 := by
  apply lratCheckerSound f806 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p806
  · intro a ha; simp [p806] at ha; subst a; trivial
  · exact checked806
theorem derived806 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c806 := by
  apply localUnsat_implies_entails f806 [c766, c759, c803, c231, c804, c117, c124, c74, c805, c283, c242, c229, c159, c294, c14, c137, c295, c776, c72, c92, c349] c806 unsat806 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c803 := derived803 a h
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c804 := derived804 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c805 := derived805 a h
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c242 := h 241 (by decide)
  have h11 : Entails.eval a c229 := h 228 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c294 := h 293 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c776 := derived776 a h
  have h18 : Entails.eval a c72 := h 71 (by decide)
  have h19 : Entails.eval a c92 := h 91 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c807 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f807 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c800, some c806, some c259, some c138, some c766, some c759, some c117, some c124, some c74, some c805, some c283, some c242, some c257, some c229, some c159, some c294, some c295, some c14, some c776, some c25, some c94, some c72, some c278, some c344, some c368, some c151, some c175, some c217, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p807 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked807 : lratChecker f807 p807 = .success := by decide +kernel
theorem unsat807 : Unsatisfiable (PosFin 57) f807 := by
  apply lratCheckerSound f807 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p807
  · intro a ha; simp [p807] at ha; subst a; trivial
  · exact checked807
theorem derived807 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c807 := by
  apply localUnsat_implies_entails f807 [c800, c806, c259, c138, c766, c759, c117, c124, c74, c805, c283, c242, c257, c229, c159, c294, c295, c14, c776, c25, c94, c72, c278, c344, c368, c151, c175, c217] c807 unsat807 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c806 := derived806 a h
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c766 := derived766 a h
  have h5 : Entails.eval a c759 := derived759 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c805 := derived805 a h
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c242 := h 241 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c294 := h 293 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c776 := derived776 a h
  have h19 : Entails.eval a c25 := h 24 (by decide)
  have h20 : Entails.eval a c94 := h 93 (by decide)
  have h21 : Entails.eval a c72 := h 71 (by decide)
  have h22 : Entails.eval a c278 := h 277 (by decide)
  have h23 : Entails.eval a c344 := h 343 (by decide)
  have h24 : Entails.eval a c368 := h 367 (by decide)
  have h25 : Entails.eval a c151 := h 150 (by decide)
  have h26 : Entails.eval a c175 := h 174 (by decide)
  have h27 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c808 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f808 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c25, some c262, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p808 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked808 : lratChecker f808 p808 = .success := by decide +kernel
theorem unsat808 : Unsatisfiable (PosFin 57) f808 := by
  apply lratCheckerSound f808 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p808
  · intro a ha; simp [p808] at ha; subst a; trivial
  · exact checked808
theorem derived808 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c808 := by
  apply localUnsat_implies_entails f808 [c65, c25, c262] c808 unsat808 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c809 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f809 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c111, some c39, some c270, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p809 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked809 : lratChecker f809 p809 = .success := by decide +kernel
theorem unsat809 : Unsatisfiable (PosFin 57) f809 := by
  apply lratCheckerSound f809 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p809
  · intro a ha; simp [p809] at ha; subst a; trivial
  · exact checked809
theorem derived809 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c809 := by
  apply localUnsat_implies_entails f809 [c659, c111, c39, c270] c809 unsat809 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c810 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f810 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c800, some c806, some c259, some c766, some c759, some c807, some c91, some c51, some c659, some c72, some c92, some c247, some c24, some c298, some c808, some c735, some c133, some c276, some c257, some c229, some c809, some c123, some c100, some c60, some c306, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p810 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked810 : lratChecker f810 p810 = .success := by decide +kernel
theorem unsat810 : Unsatisfiable (PosFin 57) f810 := by
  apply lratCheckerSound f810 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p810
  · intro a ha; simp [p810] at ha; subst a; trivial
  · exact checked810
theorem derived810 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c810 := by
  apply localUnsat_implies_entails f810 [c800, c806, c259, c766, c759, c807, c91, c51, c659, c72, c92, c247, c24, c298, c808, c735, c133, c276, c257, c229, c809, c123, c100, c60, c306] c810 unsat810 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c806 := derived806 a h
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c766 := derived766 a h
  have h4 : Entails.eval a c759 := derived759 a h
  have h5 : Entails.eval a c807 := derived807 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c659 := derived659 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c298 := h 297 (by decide)
  have h14 : Entails.eval a c808 := derived808 a h
  have h15 : Entails.eval a c735 := derived735 a h
  have h16 : Entails.eval a c133 := h 132 (by decide)
  have h17 : Entails.eval a c276 := h 275 (by decide)
  have h18 : Entails.eval a c257 := h 256 (by decide)
  have h19 : Entails.eval a c229 := h 228 (by decide)
  have h20 : Entails.eval a c809 := derived809 a h
  have h21 : Entails.eval a c123 := h 122 (by decide)
  have h22 : Entails.eval a c100 := h 99 (by decide)
  have h23 : Entails.eval a c60 := h 59 (by decide)
  have h24 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c811 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f811 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c800, some c766, some c759, some c806, some c259, some c810, some c328, some c24, some c52, some c278, some c247, some c710, some c51, some c159, some c117, some c124, some c14, some c25, some c805, some c170, some c295, some c283, some c257, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p811 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked811 : lratChecker f811 p811 = .success := by decide +kernel
theorem unsat811 : Unsatisfiable (PosFin 57) f811 := by
  apply lratCheckerSound f811 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p811
  · intro a ha; simp [p811] at ha; subst a; trivial
  · exact checked811
theorem derived811 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c811 := by
  apply localUnsat_implies_entails f811 [c800, c766, c759, c806, c259, c810, c328, c24, c52, c278, c247, c710, c51, c159, c117, c124, c14, c25, c805, c170, c295, c283, c257] c811 unsat811 (by rfl) a
  have h0 : Entails.eval a c800 := derived800 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c759 := derived759 a h
  have h3 : Entails.eval a c806 := derived806 a h
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c810 := derived810 a h
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c710 := derived710 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c124 := h 123 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c805 := derived805 a h
  have h19 : Entails.eval a c170 := h 169 (by decide)
  have h20 : Entails.eval a c295 := h 294 (by decide)
  have h21 : Entails.eval a c283 := h 282 (by decide)
  have h22 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c812 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f812 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c811, some c766, some c759, some c117, some c65, some c313, some c124, some c329, some c24, some c327, some c800, some c278, some c805, some c25, some c283, some c229, some c296, some c312, some c382, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p812 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked812 : lratChecker f812 p812 = .success := by decide +kernel
theorem unsat812 : Unsatisfiable (PosFin 57) f812 := by
  apply lratCheckerSound f812 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p812
  · intro a ha; simp [p812] at ha; subst a; trivial
  · exact checked812
theorem derived812 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c812 := by
  apply localUnsat_implies_entails f812 [c811, c766, c759, c117, c65, c313, c124, c329, c24, c327, c800, c278, c805, c25, c283, c229, c296, c312, c382] c812 unsat812 (by rfl) a
  have h0 : Entails.eval a c811 := derived811 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c759 := derived759 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c327 := h 326 (by decide)
  have h10 : Entails.eval a c800 := derived800 a h
  have h11 : Entails.eval a c278 := h 277 (by decide)
  have h12 : Entails.eval a c805 := derived805 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c229 := h 228 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c813 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f813 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c811, some c329, some c327, some c800, some c759, some c117, some c124, some c74, some c812, some c259, some c139, some c14, some c170, some c129, some c157, some c696, some c369, some c241, some c801, some c75, some c174, some c38, some c130, some c13, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p813 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked813 : lratChecker f813 p813 = .success := by decide +kernel
theorem unsat813 : Unsatisfiable (PosFin 57) f813 := by
  apply lratCheckerSound f813 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p813
  · intro a ha; simp [p813] at ha; subst a; trivial
  · exact checked813
theorem derived813 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c813 := by
  apply localUnsat_implies_entails f813 [c766, c811, c329, c327, c800, c759, c117, c124, c74, c812, c259, c139, c14, c170, c129, c157, c696, c369, c241, c801, c75, c174, c38, c130, c13] c813 unsat813 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c811 := derived811 a h
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c800 := derived800 a h
  have h5 : Entails.eval a c759 := derived759 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c74 := h 73 (by decide)
  have h9 : Entails.eval a c812 := derived812 a h
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c129 := h 128 (by decide)
  have h15 : Entails.eval a c157 := h 156 (by decide)
  have h16 : Entails.eval a c696 := derived696 a h
  have h17 : Entails.eval a c369 := h 368 (by decide)
  have h18 : Entails.eval a c241 := h 240 (by decide)
  have h19 : Entails.eval a c801 := derived801 a h
  have h20 : Entails.eval a c75 := h 74 (by decide)
  have h21 : Entails.eval a c174 := h 173 (by decide)
  have h22 : Entails.eval a c38 := h 37 (by decide)
  have h23 : Entails.eval a c130 := h 129 (by decide)
  have h24 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c814 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f814 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c811, some c766, some c800, some c813, some c91, some c313, some c65, some c659, some c92, some c329, some c52, some c24, some c31, some c247, some c759, some c804, some c349, some c801, some c769, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p814 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked814 : lratChecker f814 p814 = .success := by decide +kernel
theorem unsat814 : Unsatisfiable (PosFin 57) f814 := by
  apply lratCheckerSound f814 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p814
  · intro a ha; simp [p814] at ha; subst a; trivial
  · exact checked814
theorem derived814 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c814 := by
  apply localUnsat_implies_entails f814 [c811, c766, c800, c813, c91, c313, c65, c659, c92, c329, c52, c24, c31, c247, c759, c804, c349, c801, c769] c814 unsat814 (by rfl) a
  have h0 : Entails.eval a c811 := derived811 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c247 := h 246 (by decide)
  have h14 : Entails.eval a c759 := derived759 a h
  have h15 : Entails.eval a c804 := derived804 a h
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c801 := derived801 a h
  have h18 : Entails.eval a c769 := derived769 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c815 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f815 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c59, some c111, some c321, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p815 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked815 : lratChecker f815 p815 = .success := by decide +kernel
theorem unsat815 : Unsatisfiable (PosFin 57) f815 := by
  apply lratCheckerSound f815 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p815
  · intro a ha; simp [p815] at ha; subst a; trivial
  · exact checked815
theorem derived815 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c815 := by
  apply localUnsat_implies_entails f815 [c659, c59, c111, c321] c815 unsat815 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c816 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨54, by decide⟩, true), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨23, by decide⟩, false), (⟨55, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f816 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c270, some c398, some c253, some c380, some c389, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p816 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked816 : lratChecker f816 p816 = .success := by decide +kernel
theorem unsat816 : Unsatisfiable (PosFin 57) f816 := by
  apply lratCheckerSound f816 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p816
  · intro a ha; simp [p816] at ha; subst a; trivial
  · exact checked816
theorem derived816 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c816 := by
  apply localUnsat_implies_entails f816 [c270, c398, c253, c380, c389] c816 unsat816 (by rfl) a
  have h0 : Entails.eval a c270 := h 269 (by decide)
  have h1 : Entails.eval a c398 := h 397 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c817 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨36, by decide⟩, false), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨49, by decide⟩, true), (⟨23, by decide⟩, false), (⟨55, by decide⟩, false), (⟨33, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f817 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c816, some c352, some c376, some c343, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p817 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked817 : lratChecker f817 p817 = .success := by decide +kernel
theorem unsat817 : Unsatisfiable (PosFin 57) f817 := by
  apply lratCheckerSound f817 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p817
  · intro a ha; simp [p817] at ha; subst a; trivial
  · exact checked817
theorem derived817 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c817 := by
  apply localUnsat_implies_entails f817 [c816, c352, c376, c343] c817 unsat817 (by rfl) a
  have h0 : Entails.eval a c816 := derived816 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c818 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f818 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c759, some c766, some c800, some c811, some c327, some c329, some c24, some c52, some c813, some c91, some c31, some c659, some c313, some c278, some c247, some c65, some c814, some c138, some c735, some c815, some c123, some c100, some c80, some c113, some c61, some c817, some c395, some c323, some c208, some c351, some c229, some c143, some c368, some c243, some c292, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p818 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked818 : lratChecker f818 p818 = .success := by decide +kernel
theorem unsat818 : Unsatisfiable (PosFin 57) f818 := by
  apply lratCheckerSound f818 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p818
  · intro a ha; simp [p818] at ha; subst a; trivial
  · exact checked818
theorem derived818 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c818 := by
  apply localUnsat_implies_entails f818 [c759, c766, c800, c811, c327, c329, c24, c52, c813, c91, c31, c659, c313, c278, c247, c65, c814, c138, c735, c815, c123, c100, c80, c113, c61, c817, c395, c323, c208, c351, c229, c143, c368, c243, c292] c818 unsat818 (by rfl) a
  have h0 : Entails.eval a c759 := derived759 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c800 := derived800 a h
  have h3 : Entails.eval a c811 := derived811 a h
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c659 := derived659 a h
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c278 := h 277 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c814 := derived814 a h
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c735 := derived735 a h
  have h19 : Entails.eval a c815 := derived815 a h
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c100 := h 99 (by decide)
  have h22 : Entails.eval a c80 := h 79 (by decide)
  have h23 : Entails.eval a c113 := h 112 (by decide)
  have h24 : Entails.eval a c61 := h 60 (by decide)
  have h25 : Entails.eval a c817 := derived817 a h
  have h26 : Entails.eval a c395 := h 394 (by decide)
  have h27 : Entails.eval a c323 := h 322 (by decide)
  have h28 : Entails.eval a c208 := h 207 (by decide)
  have h29 : Entails.eval a c351 := h 350 (by decide)
  have h30 : Entails.eval a c229 := h 228 (by decide)
  have h31 : Entails.eval a c143 := h 142 (by decide)
  have h32 : Entails.eval a c368 := h 367 (by decide)
  have h33 : Entails.eval a c243 := h 242 (by decide)
  have h34 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c819 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨23, by decide⟩, false), (⟨55, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f819 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c423, some c386, some c270, some c253, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p819 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked819 : lratChecker f819 p819 = .success := by decide +kernel
theorem unsat819 : Unsatisfiable (PosFin 57) f819 := by
  apply lratCheckerSound f819 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p819
  · intro a ha; simp [p819] at ha; subst a; trivial
  · exact checked819
theorem derived819 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c819 := by
  apply localUnsat_implies_entails f819 [c371, c423, c386, c270, c253] c819 unsat819 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c423 := derived423 a h
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c820 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, false), (⟨25, by decide⟩, true), (⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨23, by decide⟩, false), (⟨55, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f820 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c138, some c395, some c819, some c262, some c197, some c125, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p820 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked820 : lratChecker f820 p820 = .success := by decide +kernel
theorem unsat820 : Unsatisfiable (PosFin 57) f820 := by
  apply lratCheckerSound f820 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p820
  · intro a ha; simp [p820] at ha; subst a; trivial
  · exact checked820
theorem derived820 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c820 := by
  apply localUnsat_implies_entails f820 [c138, c395, c819, c262, c197, c125] c820 unsat820 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c395 := h 394 (by decide)
  have h2 : Entails.eval a c819 := derived819 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c821 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨25, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f821 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c659, some c72, some c818, some c92, some c338, some c364, some c365, some c31, some c100, some c80, some c113, some c820, some c816, some c356, some c376, some c343, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p821 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked821 : lratChecker f821 p821 = .success := by decide +kernel
theorem unsat821 : Unsatisfiable (PosFin 57) f821 := by
  apply lratCheckerSound f821 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p821
  · intro a ha; simp [p821] at ha; subst a; trivial
  · exact checked821
theorem derived821 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c821 := by
  apply localUnsat_implies_entails f821 [c91, c659, c72, c818, c92, c338, c364, c365, c31, c100, c80, c113, c820, c816, c356, c376, c343] c821 unsat821 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c818 := derived818 a h
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c820 := derived820 a h
  have h13 : Entails.eval a c816 := derived816 a h
  have h14 : Entails.eval a c356 := h 355 (by decide)
  have h15 : Entails.eval a c376 := h 375 (by decide)
  have h16 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c822 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨39, by decide⟩, true), (⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f822 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c77, some c342, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p822 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked822 : lratChecker f822 p822 = .success := by decide +kernel
theorem unsat822 : Unsatisfiable (PosFin 57) f822 := by
  apply lratCheckerSound f822 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p822
  · intro a ha; simp [p822] at ha; subst a; trivial
  · exact checked822
theorem derived822 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c822 := by
  apply localUnsat_implies_entails f822 [c97, c77, c342] c822 unsat822 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c823 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f823 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c91, some c659, some c72, some c365, some c364, some c84, some c92, some c822, some c121, some c51, some c338, some c31, some c138, some c821, some c781, some c329, some c85, some c24, some c2, some c278, some c683, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p823 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked823 : lratChecker f823 p823 = .success := by decide +kernel
theorem unsat823 : Unsatisfiable (PosFin 57) f823 := by
  apply lratCheckerSound f823 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p823
  · intro a ha; simp [p823] at ha; subst a; trivial
  · exact checked823
theorem derived823 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c823 := by
  apply localUnsat_implies_entails f823 [c818, c91, c659, c72, c365, c364, c84, c92, c822, c121, c51, c338, c31, c138, c821, c781, c329, c85, c24, c2, c278, c683] c823 unsat823 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c364 := h 363 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c822 := derived822 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c821 := derived821 a h
  have h15 : Entails.eval a c781 := derived781 a h
  have h16 : Entails.eval a c329 := h 328 (by decide)
  have h17 : Entails.eval a c85 := h 84 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c278 := h 277 (by decide)
  have h21 : Entails.eval a c683 := derived683 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c824 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨42, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨55, by decide⟩, false), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f824 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c7, some c184, some c188, some c2, some c198, some c85, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p824 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked824 : lratChecker f824 p824 = .success := by decide +kernel
theorem unsat824 : Unsatisfiable (PosFin 57) f824 := by
  apply lratCheckerSound f824 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p824
  · intro a ha; simp [p824] at ha; subst a; trivial
  · exact checked824
theorem derived824 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c824 := by
  apply localUnsat_implies_entails f824 [c7, c184, c188, c2, c198, c85] c824 unsat824 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c825 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f825 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c91, some c659, some c72, some c92, some c365, some c364, some c338, some c84, some c822, some c121, some c100, some c823, some c387, some c824, some c130, some c309, some c307, some c61, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p825 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked825 : lratChecker f825 p825 = .success := by decide +kernel
theorem unsat825 : Unsatisfiable (PosFin 57) f825 := by
  apply lratCheckerSound f825 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p825
  · intro a ha; simp [p825] at ha; subst a; trivial
  · exact checked825
theorem derived825 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c825 := by
  apply localUnsat_implies_entails f825 [c818, c91, c659, c72, c92, c365, c364, c338, c84, c822, c121, c100, c823, c387, c824, c130, c309, c307, c61] c825 unsat825 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c822 := derived822 a h
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c823 := derived823 a h
  have h13 : Entails.eval a c387 := h 386 (by decide)
  have h14 : Entails.eval a c824 := derived824 a h
  have h15 : Entails.eval a c130 := h 129 (by decide)
  have h16 : Entails.eval a c309 := h 308 (by decide)
  have h17 : Entails.eval a c307 := h 306 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c826 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f826 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c307, some c387, some c51, some c71, some c659, some c72, some c92, some c338, some c309, some c24, some c815, some c61, some c235, some c120, some c248, some c77, some c239, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p826 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked826 : lratChecker f826 p826 = .success := by decide +kernel
theorem unsat826 : Unsatisfiable (PosFin 57) f826 := by
  apply lratCheckerSound f826 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p826
  · intro a ha; simp [p826] at ha; subst a; trivial
  · exact checked826
theorem derived826 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c826 := by
  apply localUnsat_implies_entails f826 [c307, c387, c51, c71, c659, c72, c92, c338, c309, c24, c815, c61, c235, c120, c248, c77, c239] c826 unsat826 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c387 := h 386 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c815 := derived815 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c77 := h 76 (by decide)
  have h16 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c827 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f827 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c307, some c826, some c365, some c363, some c690, some c761, some c72, some c52, some c793, some c659, some c328, some c325, some c123, some c55, some c112, some c81, some c347, some c181, some c360, some c1, some c207, some c163, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p827 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked827 : lratChecker f827 p827 = .success := by decide +kernel
theorem unsat827 : Unsatisfiable (PosFin 57) f827 := by
  apply lratCheckerSound f827 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p827
  · intro a ha; simp [p827] at ha; subst a; trivial
  · exact checked827
theorem derived827 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c827 := by
  apply localUnsat_implies_entails f827 [c307, c826, c365, c363, c690, c761, c72, c52, c793, c659, c328, c325, c123, c55, c112, c81, c347, c181, c360, c1, c207, c163] c827 unsat827 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c826 := derived826 a h
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c690 := derived690 a h
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c793 := derived793 a h
  have h9 : Entails.eval a c659 := derived659 a h
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c347 := h 346 (by decide)
  have h17 : Entails.eval a c181 := h 180 (by decide)
  have h18 : Entails.eval a c360 := h 359 (by decide)
  have h19 : Entails.eval a c1 := h 0 (by decide)
  have h20 : Entails.eval a c207 := h 206 (by decide)
  have h21 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c828 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨44, by decide⟩, true), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f828 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c365, some c690, some c761, some c793, some c101, some c123, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p828 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked828 : lratChecker f828 p828 = .success := by decide +kernel
theorem unsat828 : Unsatisfiable (PosFin 57) f828 := by
  apply lratCheckerSound f828 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p828
  · intro a ha; simp [p828] at ha; subst a; trivial
  · exact checked828
theorem derived828 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c828 := by
  apply localUnsat_implies_entails f828 [c365, c690, c761, c793, c101, c123] c828 unsat828 (by rfl) a
  have h0 : Entails.eval a c365 := h 364 (by decide)
  have h1 : Entails.eval a c690 := derived690 a h
  have h2 : Entails.eval a c761 := derived761 a h
  have h3 : Entails.eval a c793 := derived793 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c829 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f829 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c827, some c828, some c71, some c659, some c72, some c92, some c364, some c338, some c388, some c309, some c183, some c24, some c235, some c683, some c248, some c250, some c198, some c507, some c373, some c265, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p829 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked829 : lratChecker f829 p829 = .success := by decide +kernel
theorem unsat829 : Unsatisfiable (PosFin 57) f829 := by
  apply lratCheckerSound f829 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p829
  · intro a ha; simp [p829] at ha; subst a; trivial
  · exact checked829
theorem derived829 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c829 := by
  apply localUnsat_implies_entails f829 [c827, c828, c71, c659, c72, c92, c364, c338, c388, c309, c183, c24, c235, c683, c248, c250, c198, c507, c373, c265] c829 unsat829 (by rfl) a
  have h0 : Entails.eval a c827 := derived827 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c235 := h 234 (by decide)
  have h13 : Entails.eval a c683 := derived683 a h
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c507 := derived507 a h
  have h18 : Entails.eval a c373 := h 372 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c830 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f830 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c825, some c818, some c130, some c829, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p830 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked830 : lratChecker f830 p830 = .success := by decide +kernel
theorem unsat830 : Unsatisfiable (PosFin 57) f830 := by
  apply lratCheckerSound f830 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p830
  · intro a ha; simp [p830] at ha; subst a; trivial
  · exact checked830
theorem derived830 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c830 := by
  apply localUnsat_implies_entails f830 [c825, c818, c130, c829] c830 unsat830 (by rfl) a
  have h0 : Entails.eval a c825 := derived825 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c829 := derived829 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c831 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f831 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c659, some c72, some c92, some c364, some c338, some c309, some c84, some c24, some c235, some c25, some c683, some c2, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p831 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked831 : lratChecker f831 p831 = .success := by decide +kernel
theorem unsat831 : Unsatisfiable (PosFin 57) f831 := by
  apply lratCheckerSound f831 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p831
  · intro a ha; simp [p831] at ha; subst a; trivial
  · exact checked831
theorem derived831 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c831 := by
  apply localUnsat_implies_entails f831 [c71, c659, c72, c92, c364, c338, c309, c84, c24, c235, c25, c683, c2] c831 unsat831 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c683 := derived683 a h
  have h12 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c832 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f832 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c831, some c365, some c690, some c337, some c761, some c828, some c72, some c52, some c793, some c387, some c307, some c659, some c328, some c325, some c123, some c55, some c116, some c2, some c163, some c184, some c216, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p832 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked832 : lratChecker f832 p832 = .success := by decide +kernel
theorem unsat832 : Unsatisfiable (PosFin 57) f832 := by
  apply lratCheckerSound f832 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p832
  · intro a ha; simp [p832] at ha; subst a; trivial
  · exact checked832
theorem derived832 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c832 := by
  apply localUnsat_implies_entails f832 [c831, c365, c690, c337, c761, c828, c72, c52, c793, c387, c307, c659, c328, c325, c123, c55, c116, c2, c163, c184, c216] c832 unsat832 (by rfl) a
  have h0 : Entails.eval a c831 := derived831 a h
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c690 := derived690 a h
  have h3 : Entails.eval a c337 := h 336 (by decide)
  have h4 : Entails.eval a c761 := derived761 a h
  have h5 : Entails.eval a c828 := derived828 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c793 := derived793 a h
  have h9 : Entails.eval a c387 := h 386 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c659 := derived659 a h
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c325 := h 324 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c55 := h 54 (by decide)
  have h16 : Entails.eval a c116 := h 115 (by decide)
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c163 := h 162 (by decide)
  have h19 : Entails.eval a c184 := h 183 (by decide)
  have h20 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c833 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f833 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c112, some c133, some c184, some c234, some c263, some c7, some c40, some c371, some c37, some c265, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p833 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked833 : lratChecker f833 p833 = .success := by decide +kernel
theorem unsat833 : Unsatisfiable (PosFin 57) f833 := by
  apply lratCheckerSound f833 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p833
  · intro a ha; simp [p833] at ha; subst a; trivial
  · exact checked833
theorem derived833 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c833 := by
  apply localUnsat_implies_entails f833 [c659, c112, c133, c184, c234, c263, c7, c40, c371, c37, c265] c833 unsat833 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c234 := h 233 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c834 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨33, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f834 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c833, some c2, some c85, some c25, some c263, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p834 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked834 : lratChecker f834 p834 = .success := by decide +kernel
theorem unsat834 : Unsatisfiable (PosFin 57) f834 := by
  apply lratCheckerSound f834 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p834
  · intro a ha; simp [p834] at ha; subst a; trivial
  · exact checked834
theorem derived834 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c834 := by
  apply localUnsat_implies_entails f834 [c833, c2, c85, c25, c263] c834 unsat834 (by rfl) a
  have h0 : Entails.eval a c833 := derived833 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c835 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨39, by decide⟩, false), (⟨42, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f835 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c365, some c72, some c337, some c690, some c32, some c793, some c123, some c834, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p835 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked835 : lratChecker f835 p835 = .success := by decide +kernel
theorem unsat835 : Unsatisfiable (PosFin 57) f835 := by
  apply lratCheckerSound f835 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p835
  · intro a ha; simp [p835] at ha; subst a; trivial
  · exact checked835
theorem derived835 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c835 := by
  apply localUnsat_implies_entails f835 [c365, c72, c337, c690, c32, c793, c123, c834] c835 unsat835 (by rfl) a
  have h0 : Entails.eval a c365 := h 364 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c337 := h 336 (by decide)
  have h3 : Entails.eval a c690 := derived690 a h
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c793 := derived793 a h
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c834 := derived834 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c836 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨42, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f836 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c365, some c337, some c52, some c835, some c310, some c23, some c234, some c667, some c25, some c2, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p836 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked836 : lratChecker f836 p836 = .success := by decide +kernel
theorem unsat836 : Unsatisfiable (PosFin 57) f836 := by
  apply lratCheckerSound f836 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p836
  · intro a ha; simp [p836] at ha; subst a; trivial
  · exact checked836
theorem derived836 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c836 := by
  apply localUnsat_implies_entails f836 [c365, c337, c52, c835, c310, c23, c234, c667, c25, c2] c836 unsat836 (by rfl) a
  have h0 : Entails.eval a c365 := h 364 (by decide)
  have h1 : Entails.eval a c337 := h 336 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c835 := derived835 a h
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c667 := derived667 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c837 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f837 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c71, some c659, some c72, some c92, some c338, some c310, some c24, some c235, some c25, some c683, some c2, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p837 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked837 : lratChecker f837 p837 = .success := by decide +kernel
theorem unsat837 : Unsatisfiable (PosFin 57) f837 := by
  apply lratCheckerSound f837 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p837
  · intro a ha; simp [p837] at ha; subst a; trivial
  · exact checked837
theorem derived837 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c837 := by
  apply localUnsat_implies_entails f837 [c51, c71, c659, c72, c92, c338, c310, c24, c235, c25, c683, c2] c837 unsat837 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c235 := h 234 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c683 := derived683 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c838 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f838 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c825, some c818, some c830, some c832, some c22, some c837, some c365, some c690, some c836, some c388, some c387, some c793, some c101, some c123, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p838 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked838 : lratChecker f838 p838 = .success := by decide +kernel
theorem unsat838 : Unsatisfiable (PosFin 57) f838 := by
  apply lratCheckerSound f838 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p838
  · intro a ha; simp [p838] at ha; subst a; trivial
  · exact checked838
theorem derived838 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c838 := by
  apply localUnsat_implies_entails f838 [c825, c818, c830, c832, c22, c837, c365, c690, c836, c388, c387, c793, c101, c123] c838 unsat838 (by rfl) a
  have h0 : Entails.eval a c825 := derived825 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c830 := derived830 a h
  have h3 : Entails.eval a c832 := derived832 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c837 := derived837 a h
  have h6 : Entails.eval a c365 := h 364 (by decide)
  have h7 : Entails.eval a c690 := derived690 a h
  have h8 : Entails.eval a c836 := derived836 a h
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c793 := derived793 a h
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c839 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, false), (⟨48, by decide⟩, true), (⟨5, by decide⟩, false), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f839 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c182, some c190, some c10, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p839 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked839 : lratChecker f839 p839 = .success := by decide +kernel
theorem unsat839 : Unsatisfiable (PosFin 57) f839 := by
  apply lratCheckerSound f839 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p839
  · intro a ha; simp [p839] at ha; subst a; trivial
  · exact checked839
theorem derived839 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c839 := by
  apply localUnsat_implies_entails f839 [c182, c190, c10] c839 unsat839 (by rfl) a
  have h0 : Entails.eval a c182 := h 181 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c840 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨14, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f840 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c793, some c123, some c101, some c81, some c386, some c340, some c839, some c213, some c217, some c185, some c175, some c10, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p840 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked840 : lratChecker f840 p840 = .success := by decide +kernel
theorem unsat840 : Unsatisfiable (PosFin 57) f840 := by
  apply lratCheckerSound f840 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p840
  · intro a ha; simp [p840] at ha; subst a; trivial
  · exact checked840
theorem derived840 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c840 := by
  apply localUnsat_implies_entails f840 [c793, c123, c101, c81, c386, c340, c839, c213, c217, c185, c175, c10] c840 unsat840 (by rfl) a
  have h0 : Entails.eval a c793 := derived793 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c386 := h 385 (by decide)
  have h5 : Entails.eval a c340 := h 339 (by decide)
  have h6 : Entails.eval a c839 := derived839 a h
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c175 := h 174 (by decide)
  have h11 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c841 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨47, by decide⟩, false), (⟨7, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f841 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c837, some c365, some c363, some c690, some c337, some c836, some c52, some c840, some c310, some c23, some c234, some c667, some c25, some c2, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p841 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked841 : lratChecker f841 p841 = .success := by decide +kernel
theorem unsat841 : Unsatisfiable (PosFin 57) f841 := by
  apply lratCheckerSound f841 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p841
  · intro a ha; simp [p841] at ha; subst a; trivial
  · exact checked841
theorem derived841 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c841 := by
  apply localUnsat_implies_entails f841 [c837, c365, c363, c690, c337, c836, c52, c840, c310, c23, c234, c667, c25, c2] c841 unsat841 (by rfl) a
  have h0 : Entails.eval a c837 := derived837 a h
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c690 := derived690 a h
  have h4 : Entails.eval a c337 := h 336 (by decide)
  have h5 : Entails.eval a c836 := derived836 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c840 := derived840 a h
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c234 := h 233 (by decide)
  have h11 : Entails.eval a c667 := derived667 a h
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c842 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f842 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c825, some c838, some c138, some c30, some c841, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p842 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked842 : lratChecker f842 p842 = .success := by decide +kernel
theorem unsat842 : Unsatisfiable (PosFin 57) f842 := by
  apply lratCheckerSound f842 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p842
  · intro a ha; simp [p842] at ha; subst a; trivial
  · exact checked842
theorem derived842 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c842 := by
  apply localUnsat_implies_entails f842 [c818, c825, c838, c138, c30, c841] c842 unsat842 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c825 := derived825 a h
  have h2 : Entails.eval a c838 := derived838 a h
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c843 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨47, by decide⟩, false), (⟨7, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f843 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c365, some c690, some c337, some c117, some c124, some c79, some c94, some c345, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p843 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked843 : lratChecker f843 p843 = .success := by decide +kernel
theorem unsat843 : Unsatisfiable (PosFin 57) f843 := by
  apply lratCheckerSound f843 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p843
  · intro a ha; simp [p843] at ha; subst a; trivial
  · exact checked843
theorem derived843 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c843 := by
  apply localUnsat_implies_entails f843 [c365, c690, c337, c117, c124, c79, c94, c345] c843 unsat843 (by rfl) a
  have h0 : Entails.eval a c365 := h 364 (by decide)
  have h1 : Entails.eval a c690 := derived690 a h
  have h2 : Entails.eval a c337 := h 336 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c844 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f844 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c25, some c94, some c392, some c390, some c257, some c380, some c260, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p844 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked844 : lratChecker f844 p844 = .success := by decide +kernel
theorem unsat844 : Unsatisfiable (PosFin 57) f844 := by
  apply lratCheckerSound f844 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p844
  · intro a ha; simp [p844] at ha; subst a; trivial
  · exact checked844
theorem derived844 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c844 := by
  apply localUnsat_implies_entails f844 [c85, c25, c94, c392, c390, c257, c380, c260] c844 unsat844 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c392 := h 391 (by decide)
  have h4 : Entails.eval a c390 := h 389 (by decide)
  have h5 : Entails.eval a c257 := h 256 (by decide)
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c845 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨49, by decide⟩, true), (⟨21, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨32, by decide⟩, false), (⟨56, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f845 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c659, some c397, some c269, some c107, some c358, some c19, some c121, some c366, some c305, some c105, some c287, some c318, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p845 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked845 : lratChecker f845 p845 = .success := by decide +kernel
theorem unsat845 : Unsatisfiable (PosFin 57) f845 := by
  apply lratCheckerSound f845 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p845
  · intro a ha; simp [p845] at ha; subst a; trivial
  · exact checked845
theorem derived845 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c845 := by
  apply localUnsat_implies_entails f845 [c106, c659, c397, c269, c107, c358, c19, c121, c366, c305, c105, c287, c318] c845 unsat845 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c397 := h 396 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c366 := h 365 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c846 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨45, by decide⟩, true), (⟨35, by decide⟩, false), (⟨56, by decide⟩, false), (⟨46, by decide⟩, true), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f846 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c380, some c396, some c355, some c374, some c339, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p846 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked846 : lratChecker f846 p846 = .success := by decide +kernel
theorem unsat846 : Unsatisfiable (PosFin 57) f846 := by
  apply lratCheckerSound f846 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p846
  · intro a ha; simp [p846] at ha; subst a; trivial
  · exact checked846
theorem derived846 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c846 := by
  apply localUnsat_implies_entails f846 [c659, c380, c396, c355, c374, c339] c846 unsat846 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c396 := h 395 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c374 := h 373 (by decide)
  have h5 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c847 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨40, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f847 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c72, some c818, some c842, some c843, some c117, some c124, some c79, some c844, some c385, some c383, some c32, some c99, some c257, some c846, some c845, some c314, some c263, some c17, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p847 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked847 : lratChecker f847 p847 = .success := by decide +kernel
theorem unsat847 : Unsatisfiable (PosFin 57) f847 := by
  apply lratCheckerSound f847 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p847
  · intro a ha; simp [p847] at ha; subst a; trivial
  · exact checked847
theorem derived847 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c847 := by
  apply localUnsat_implies_entails f847 [c52, c72, c818, c842, c843, c117, c124, c79, c844, c385, c383, c32, c99, c257, c846, c845, c314, c263, c17] c847 unsat847 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c842 := derived842 a h
  have h4 : Entails.eval a c843 := derived843 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c844 := derived844 a h
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c99 := h 98 (by decide)
  have h13 : Entails.eval a c257 := h 256 (by decide)
  have h14 : Entails.eval a c846 := derived846 a h
  have h15 : Entails.eval a c845 := derived845 a h
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c263 := h 262 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c848 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨5, by decide⟩, true), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f848 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c383, some c103, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p848 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked848 : lratChecker f848 p848 = .success := by decide +kernel
theorem unsat848 : Unsatisfiable (PosFin 57) f848 := by
  apply lratCheckerSound f848 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p848
  · intro a ha; simp [p848] at ha; subst a; trivial
  · exact checked848
theorem derived848 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c848 := by
  apply localUnsat_implies_entails f848 [c385, c383, c103] c848 unsat848 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c849 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨41, by decide⟩, true), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f849 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c25, some c263, some c232, some c43, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p849 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked849 : lratChecker f849 p849 = .success := by decide +kernel
theorem unsat849 : Unsatisfiable (PosFin 57) f849 := by
  apply lratCheckerSound f849 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p849
  · intro a ha; simp [p849] at ha; subst a; trivial
  · exact checked849
theorem derived849 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c849 := by
  apply localUnsat_implies_entails f849 [c85, c25, c263, c232, c43] c849 unsat849 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c850 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f850 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c843, some c72, some c52, some c847, some c83, some c848, some c849, some c735, some c133, some c731, some c232, some c21, some c29, some c390, some c308, some c253, some c185, some c231, some c159, some c332, some c11, some c287, some c224, some c79, some c236, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p850 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked850 : lratChecker f850 p850 = .success := by decide +kernel
theorem unsat850 : Unsatisfiable (PosFin 57) f850 := by
  apply lratCheckerSound f850 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p850
  · intro a ha; simp [p850] at ha; subst a; trivial
  · exact checked850
theorem derived850 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c850 := by
  apply localUnsat_implies_entails f850 [c818, c842, c843, c72, c52, c847, c83, c848, c849, c735, c133, c731, c232, c21, c29, c390, c308, c253, c185, c231, c159, c332, c11, c287, c224, c79, c236] c850 unsat850 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c847 := derived847 a h
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c848 := derived848 a h
  have h8 : Entails.eval a c849 := derived849 a h
  have h9 : Entails.eval a c735 := derived735 a h
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c731 := derived731 a h
  have h12 : Entails.eval a c232 := h 231 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c390 := h 389 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c253 := h 252 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c231 := h 230 (by decide)
  have h20 : Entails.eval a c159 := h 158 (by decide)
  have h21 : Entails.eval a c332 := h 331 (by decide)
  have h22 : Entails.eval a c11 := h 10 (by decide)
  have h23 : Entails.eval a c287 := h 286 (by decide)
  have h24 : Entails.eval a c224 := h 223 (by decide)
  have h25 : Entails.eval a c79 := h 78 (by decide)
  have h26 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c851 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f851 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c850, some c818, some c842, some c843, some c117, some c735, some c848, some c133, some c235, some c731, some c24, some c32, some c43, some c310, some c232, some c231, some c49, some c328, some c332, some c161, some c287, some c7, some c216, some c342, some c96, some c186, some c163, some c306, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p851 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked851 : lratChecker f851 p851 = .success := by decide +kernel
theorem unsat851 : Unsatisfiable (PosFin 57) f851 := by
  apply lratCheckerSound f851 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p851
  · intro a ha; simp [p851] at ha; subst a; trivial
  · exact checked851
theorem derived851 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c851 := by
  apply localUnsat_implies_entails f851 [c850, c818, c842, c843, c117, c735, c848, c133, c235, c731, c24, c32, c43, c310, c232, c231, c49, c328, c332, c161, c287, c7, c216, c342, c96, c186, c163, c306] c851 unsat851 (by rfl) a
  have h0 : Entails.eval a c850 := derived850 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c842 := derived842 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c735 := derived735 a h
  have h6 : Entails.eval a c848 := derived848 a h
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c235 := h 234 (by decide)
  have h9 : Entails.eval a c731 := derived731 a h
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c310 := h 309 (by decide)
  have h14 : Entails.eval a c232 := h 231 (by decide)
  have h15 : Entails.eval a c231 := h 230 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c332 := h 331 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c287 := h 286 (by decide)
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c216 := h 215 (by decide)
  have h23 : Entails.eval a c342 := h 341 (by decide)
  have h24 : Entails.eval a c96 := h 95 (by decide)
  have h25 : Entails.eval a c186 := h 185 (by decide)
  have h26 : Entails.eval a c163 := h 162 (by decide)
  have h27 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c852 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f852 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c85, some c25, some c235, some c24, some c32, some c310, some c294, some c159, some c328, some c332, some c287, some c53, some c342, some c7, some c184, some c197, some c198, some c362, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p852 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked852 : lratChecker f852 p852 = .success := by decide +kernel
theorem unsat852 : Unsatisfiable (PosFin 57) f852 := by
  apply lratCheckerSound f852 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p852
  · intro a ha; simp [p852] at ha; subst a; trivial
  · exact checked852
theorem derived852 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c852 := by
  apply localUnsat_implies_entails f852 [c364, c85, c25, c235, c24, c32, c310, c294, c159, c328, c332, c287, c53, c342, c7, c184, c197, c198, c362] c852 unsat852 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  have h8 : Entails.eval a c159 := h 158 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c332 := h 331 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c342 := h 341 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c184 := h 183 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c198 := h 197 (by decide)
  have h18 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c853 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f853 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c843, some c850, some c364, some c851, some c852, some c385, some c383, some c848, some c92, some c32, some c257, some c124, some c659, some c235, some c362, some c34, some c392, some c396, some c282, some c105, some c35, some c121, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p853 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked853 : lratChecker f853 p853 = .success := by decide +kernel
theorem unsat853 : Unsatisfiable (PosFin 57) f853 := by
  apply lratCheckerSound f853 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p853
  · intro a ha; simp [p853] at ha; subst a; trivial
  · exact checked853
theorem derived853 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c853 := by
  apply localUnsat_implies_entails f853 [c818, c842, c843, c850, c364, c851, c852, c385, c383, c848, c92, c32, c257, c124, c659, c235, c362, c34, c392, c396, c282, c105, c35, c121] c853 unsat853 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c850 := derived850 a h
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c851 := derived851 a h
  have h6 : Entails.eval a c852 := derived852 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c848 := derived848 a h
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c659 := derived659 a h
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c362 := h 361 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c392 := h 391 (by decide)
  have h19 : Entails.eval a c396 := h 395 (by decide)
  have h20 : Entails.eval a c282 := h 281 (by decide)
  have h21 : Entails.eval a c105 := h 104 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c854 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f854 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c852, some c385, some c32, some c235, some c17, some c297, some c296, some c294, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p854 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked854 : lratChecker f854 p854 = .success := by decide +kernel
theorem unsat854 : Unsatisfiable (PosFin 57) f854 := by
  apply lratCheckerSound f854 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p854
  · intro a ha; simp [p854] at ha; subst a; trivial
  · exact checked854
theorem derived854 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c854 := by
  apply localUnsat_implies_entails f854 [c364, c852, c385, c32, c235, c17, c297, c296, c294] c854 unsat854 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c852 := derived852 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c235 := h 234 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c855 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f855 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c853, some c818, some c842, some c843, some c854, some c117, some c2, some c848, some c133, some c235, some c731, some c24, some c32, some c309, some c310, some c231, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p855 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked855 : lratChecker f855 p855 = .success := by decide +kernel
theorem unsat855 : Unsatisfiable (PosFin 57) f855 := by
  apply lratCheckerSound f855 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p855
  · intro a ha; simp [p855] at ha; subst a; trivial
  · exact checked855
theorem derived855 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c855 := by
  apply localUnsat_implies_entails f855 [c853, c818, c842, c843, c854, c117, c2, c848, c133, c235, c731, c24, c32, c309, c310, c231] c855 unsat855 (by rfl) a
  have h0 : Entails.eval a c853 := derived853 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c842 := derived842 a h
  have h3 : Entails.eval a c843 := derived843 a h
  have h4 : Entails.eval a c854 := derived854 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c848 := derived848 a h
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c731 := derived731 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c856 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f856 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c855, some c52, some c853, some c818, some c842, some c843, some c117, some c2, some c83, some c848, some c133, some c232, some c731, some c21, some c29, some c390, some c308, some c159, some c231, some c727, some c309, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p856 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked856 : lratChecker f856 p856 = .success := by decide +kernel
theorem unsat856 : Unsatisfiable (PosFin 57) f856 := by
  apply lratCheckerSound f856 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p856
  · intro a ha; simp [p856] at ha; subst a; trivial
  · exact checked856
theorem derived856 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c856 := by
  apply localUnsat_implies_entails f856 [c855, c52, c853, c818, c842, c843, c117, c2, c83, c848, c133, c232, c731, c21, c29, c390, c308, c159, c231, c727, c309] c856 unsat856 (by rfl) a
  have h0 : Entails.eval a c855 := derived855 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c853 := derived853 a h
  have h3 : Entails.eval a c818 := derived818 a h
  have h4 : Entails.eval a c842 := derived842 a h
  have h5 : Entails.eval a c843 := derived843 a h
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c848 := derived848 a h
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c232 := h 231 (by decide)
  have h12 : Entails.eval a c731 := derived731 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c390 := h 389 (by decide)
  have h16 : Entails.eval a c308 := h 307 (by decide)
  have h17 : Entails.eval a c159 := h 158 (by decide)
  have h18 : Entails.eval a c231 := h 230 (by decide)
  have h19 : Entails.eval a c727 := derived727 a h
  have h20 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c857 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f857 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c72, some c659, some c85, some c25, some c392, some c263, some c362, some c32, some c388, some c93, some c121, some c95, some c81, some c347, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p857 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked857 : lratChecker f857 p857 = .success := by decide +kernel
theorem unsat857 : Unsatisfiable (PosFin 57) f857 := by
  apply lratCheckerSound f857 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p857
  · intro a ha; simp [p857] at ha; subst a; trivial
  · exact checked857
theorem derived857 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c857 := by
  apply localUnsat_implies_entails f857 [c72, c659, c85, c25, c392, c263, c362, c32, c388, c93, c121, c95, c81, c347] c857 unsat857 (by rfl) a
  have h0 : Entails.eval a c72 := h 71 (by decide)
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c392 := h 391 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c858 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f858 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c843, some c853, some c855, some c72, some c659, some c856, some c857, some c336, some c848, some c362, some c124, some c392, some c396, some c79, some c355, some c105, some c366, some c121, some c81, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p858 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked858 : lratChecker f858 p858 = .success := by decide +kernel
theorem unsat858 : Unsatisfiable (PosFin 57) f858 := by
  apply lratCheckerSound f858 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p858
  · intro a ha; simp [p858] at ha; subst a; trivial
  · exact checked858
theorem derived858 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c858 := by
  apply localUnsat_implies_entails f858 [c818, c842, c843, c853, c855, c72, c659, c856, c857, c336, c848, c362, c124, c392, c396, c79, c355, c105, c366, c121, c81] c858 unsat858 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c853 := derived853 a h
  have h4 : Entails.eval a c855 := derived855 a h
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c659 := derived659 a h
  have h7 : Entails.eval a c856 := derived856 a h
  have h8 : Entails.eval a c857 := derived857 a h
  have h9 : Entails.eval a c336 := h 335 (by decide)
  have h10 : Entails.eval a c848 := derived848 a h
  have h11 : Entails.eval a c362 := h 361 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c392 := h 391 (by decide)
  have h14 : Entails.eval a c396 := h 395 (by decide)
  have h15 : Entails.eval a c79 := h 78 (by decide)
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c105 := h 104 (by decide)
  have h18 : Entails.eval a c366 := h 365 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c859 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨41, by decide⟩, true), (⟨24, by decide⟩, false), (⟨25, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f859 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c85, some c263, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p859 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked859 : lratChecker f859 p859 = .success := by decide +kernel
theorem unsat859 : Unsatisfiable (PosFin 57) f859 := by
  apply lratCheckerSound f859 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p859
  · intro a ha; simp [p859] at ha; subst a; trivial
  · exact checked859
theorem derived859 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c859 := by
  apply localUnsat_implies_entails f859 [c17, c85, c263] c859 unsat859 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c860 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f860 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c30, some c842, some c818, some c72, some c52, some c328, some c309, some c325, some c32, some c70, some c336, some c859, some c117, some c83, some c42, some c103, some c232, some c390, some c760, some c758, some c249, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p860 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked860 : lratChecker f860 p860 = .success := by decide +kernel
theorem unsat860 : Unsatisfiable (PosFin 57) f860 := by
  apply lratCheckerSound f860 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p860
  · intro a ha; simp [p860] at ha; subst a; trivial
  · exact checked860
theorem derived860 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c860 := by
  apply localUnsat_implies_entails f860 [c22, c30, c842, c818, c72, c52, c328, c309, c325, c32, c70, c336, c859, c117, c83, c42, c103, c232, c390, c760, c758, c249] c860 unsat860 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c842 := derived842 a h
  have h3 : Entails.eval a c818 := derived818 a h
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c859 := derived859 a h
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c103 := h 102 (by decide)
  have h17 : Entails.eval a c232 := h 231 (by decide)
  have h18 : Entails.eval a c390 := h 389 (by decide)
  have h19 : Entails.eval a c760 := derived760 a h
  have h20 : Entails.eval a c758 := derived758 a h
  have h21 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c861 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f861 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c858, some c818, some c860, some c364, some c70, some c22, some c842, some c843, some c117, some c848, some c42, some c82, some c232, some c133, some c736, some c712, some c92, some c103, some c308, some c325, some c63, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p861 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked861 : lratChecker f861 p861 = .success := by decide +kernel
theorem unsat861 : Unsatisfiable (PosFin 57) f861 := by
  apply lratCheckerSound f861 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p861
  · intro a ha; simp [p861] at ha; subst a; trivial
  · exact checked861
theorem derived861 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c861 := by
  apply localUnsat_implies_entails f861 [c858, c818, c860, c364, c70, c22, c842, c843, c117, c848, c42, c82, c232, c133, c736, c712, c92, c103, c308, c325, c63] c861 unsat861 (by rfl) a
  have h0 : Entails.eval a c858 := derived858 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c860 := derived860 a h
  have h3 : Entails.eval a c364 := h 363 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c842 := derived842 a h
  have h7 : Entails.eval a c843 := derived843 a h
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c848 := derived848 a h
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c232 := h 231 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  have h14 : Entails.eval a c736 := derived736 a h
  have h15 : Entails.eval a c712 := derived712 a h
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c103 := h 102 (by decide)
  have h18 : Entails.eval a c308 := h 307 (by decide)
  have h19 : Entails.eval a c325 := h 324 (by decide)
  have h20 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c862 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨54, by decide⟩, false), (⟨40, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f862 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c25, some c392, some c235, some c92, some c24, some c309, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p862 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked862 : lratChecker f862 p862 = .success := by decide +kernel
theorem unsat862 : Unsatisfiable (PosFin 57) f862 := by
  apply lratCheckerSound f862 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p862
  · intro a ha; simp [p862] at ha; subst a; trivial
  · exact checked862
theorem derived862 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c862 := by
  apply localUnsat_implies_entails f862 [c85, c25, c392, c235, c92, c24, c309] c862 unsat862 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c392 := h 391 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c863 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f863 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c858, some c30, some c22, some c860, some c364, some c70, some c861, some c862, some c385, some c296, some c92, some c32, some c582, some c392, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p863 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked863 : lratChecker f863 p863 = .success := by decide +kernel
theorem unsat863 : Unsatisfiable (PosFin 57) f863 := by
  apply lratCheckerSound f863 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p863
  · intro a ha; simp [p863] at ha; subst a; trivial
  · exact checked863
theorem derived863 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c863 := by
  apply localUnsat_implies_entails f863 [c818, c858, c30, c22, c860, c364, c70, c861, c862, c385, c296, c92, c32, c582, c392] c863 unsat863 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c858 := derived858 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c860 := derived860 a h
  have h5 : Entails.eval a c364 := h 363 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c861 := derived861 a h
  have h8 : Entails.eval a c862 := derived862 a h
  have h9 : Entails.eval a c385 := h 384 (by decide)
  have h10 : Entails.eval a c296 := h 295 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c582 := derived582 a h
  have h14 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c864 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f864 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c70, some c296, some c392, some c325, some c582, some c52, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p864 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked864 : lratChecker f864 p864 = .success := by decide +kernel
theorem unsat864 : Unsatisfiable (PosFin 57) f864 := by
  apply lratCheckerSound f864 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p864
  · intro a ha; simp [p864] at ha; subst a; trivial
  · exact checked864
theorem derived864 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c864 := by
  apply localUnsat_implies_entails f864 [c30, c70, c296, c392, c325, c582, c52] c864 unsat864 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c392 := h 391 (by decide)
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c582 := derived582 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c865 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨56, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f865 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c392, some c396, some c325, some c105, some c121, some c107, some c61, some c323, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p865 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked865 : lratChecker f865 p865 = .success := by decide +kernel
theorem unsat865 : Unsatisfiable (PosFin 57) f865 := by
  apply lratCheckerSound f865 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p865
  · intro a ha; simp [p865] at ha; subst a; trivial
  · exact checked865
theorem derived865 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c865 := by
  apply localUnsat_implies_entails f865 [c392, c396, c325, c105, c121, c107, c61, c323] c865 unsat865 (by rfl) a
  have h0 : Entails.eval a c392 := h 391 (by decide)
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c866 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨47, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f866 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c842, some c818, some c864, some c865, some c382, some c362, some c296, some c365, some c363, some c690, some c17, some c52, some c360, some c124, some c263, some c332, some c106, some c53, some c397, some c121, some c107, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p866 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked866 : lratChecker f866 p866 = .success := by decide +kernel
theorem unsat866 : Unsatisfiable (PosFin 57) f866 := by
  apply lratCheckerSound f866 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p866
  · intro a ha; simp [p866] at ha; subst a; trivial
  · exact checked866
theorem derived866 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c866 := by
  apply localUnsat_implies_entails f866 [c659, c842, c818, c864, c865, c382, c362, c296, c365, c363, c690, c17, c52, c360, c124, c263, c332, c106, c53, c397, c121, c107] c866 unsat866 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c864 := derived864 a h
  have h4 : Entails.eval a c865 := derived865 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c690 := derived690 a h
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c332 := h 331 (by decide)
  have h17 : Entails.eval a c106 := h 105 (by decide)
  have h18 : Entails.eval a c53 := h 52 (by decide)
  have h19 : Entails.eval a c397 := h 396 (by decide)
  have h20 : Entails.eval a c121 := h 120 (by decide)
  have h21 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c867 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨32, by decide⟩, false), (⟨39, by decide⟩, false), (⟨30, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f867 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c19, some c329, some c242, some c231, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p867 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked867 : lratChecker f867 p867 = .success := by decide +kernel
theorem unsat867 : Unsatisfiable (PosFin 57) f867 := by
  apply lratCheckerSound f867 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p867
  · intro a ha; simp [p867] at ha; subst a; trivial
  · exact checked867
theorem derived867 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c867 := by
  apply localUnsat_implies_entails f867 [c54, c19, c329, c242, c231] c867 unsat867 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c868 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨30, by decide⟩, true), (⟨38, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f868 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c842, some c818, some c365, some c363, some c690, some c52, some c292, some c124, some c79, some c867, some c334, some c231, some c805, some c242, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p868 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked868 : lratChecker f868 p868 = .success := by decide +kernel
theorem unsat868 : Unsatisfiable (PosFin 57) f868 := by
  apply lratCheckerSound f868 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p868
  · intro a ha; simp [p868] at ha; subst a; trivial
  · exact checked868
theorem derived868 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c868 := by
  apply localUnsat_implies_entails f868 [c842, c818, c365, c363, c690, c52, c292, c124, c79, c867, c334, c231, c805, c242] c868 unsat868 (by rfl) a
  have h0 : Entails.eval a c842 := derived842 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c690 := derived690 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c867 := derived867 a h
  have h10 : Entails.eval a c334 := h 333 (by decide)
  have h11 : Entails.eval a c231 := h 230 (by decide)
  have h12 : Entails.eval a c805 := derived805 a h
  have h13 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c869 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f869 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c863, some c842, some c32, some c866, some c22, some c868, some c362, some c392, some c396, some c210, some c375, some c105, some c355, some c610, some c121, some c340, some c386, some c107, some c190, some c99, some c208, some c11, some c179, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p869 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked869 : lratChecker f869 p869 = .success := by decide +kernel
theorem unsat869 : Unsatisfiable (PosFin 57) f869 := by
  apply lratCheckerSound f869 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p869
  · intro a ha; simp [p869] at ha; subst a; trivial
  · exact checked869
theorem derived869 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c869 := by
  apply localUnsat_implies_entails f869 [c659, c863, c842, c32, c866, c22, c868, c362, c392, c396, c210, c375, c105, c355, c610, c121, c340, c386, c107, c190, c99, c208, c11, c179] c869 unsat869 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c863 := derived863 a h
  have h2 : Entails.eval a c842 := derived842 a h
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c866 := derived866 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c868 := derived868 a h
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c396 := h 395 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c375 := h 374 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c610 := derived610 a h
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c340 := h 339 (by decide)
  have h17 : Entails.eval a c386 := h 385 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c190 := h 189 (by decide)
  have h20 : Entails.eval a c99 := h 98 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c11 := h 10 (by decide)
  have h23 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c870 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f870 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c818, some c659, some c869, some c338, some c384, some c52, some c30, some c259, some c382, some c298, some c392, some c396, some c17, some c375, some c105, some c278, some c302, some c121, some c7, some c41, some c653, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p870 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked870 : lratChecker f870 p870 = .success := by decide +kernel
theorem unsat870 : Unsatisfiable (PosFin 57) f870 := by
  apply lratCheckerSound f870 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p870
  · intro a ha; simp [p870] at ha; subst a; trivial
  · exact checked870
theorem derived870 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c870 := by
  apply localUnsat_implies_entails f870 [c863, c818, c659, c869, c338, c384, c52, c30, c259, c382, c298, c392, c396, c17, c375, c105, c278, c302, c121, c7, c41, c653] c870 unsat870 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c869 := derived869 a h
  have h4 : Entails.eval a c338 := h 337 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c298 := h 297 (by decide)
  have h11 : Entails.eval a c392 := h 391 (by decide)
  have h12 : Entails.eval a c396 := h 395 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c278 := h 277 (by decide)
  have h17 : Entails.eval a c302 := h 301 (by decide)
  have h18 : Entails.eval a c121 := h 120 (by decide)
  have h19 : Entails.eval a c7 := h 6 (by decide)
  have h20 : Entails.eval a c41 := h 40 (by decide)
  have h21 : Entails.eval a c653 := derived653 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c871 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨41, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f871 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c72, some c92, some c338, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p871 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked871 : lratChecker f871 p871 = .success := by decide +kernel
theorem unsat871 : Unsatisfiable (PosFin 57) f871 := by
  apply lratCheckerSound f871 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p871
  · intro a ha; simp [p871] at ha; subst a; trivial
  · exact checked871
theorem derived871 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c871 := by
  apply localUnsat_implies_entails f871 [c72, c92, c338] c871 unsat871 (by rfl) a
  have h0 : Entails.eval a c72 := h 71 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c872 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f872 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c842, some c818, some c871, some c659, some c870, some c364, some c336, some c30, some c382, some c392, some c396, some c105, some c121, some c107, some c81, some c367, some c355, some c479, some c690, some c397, some c124, some c106, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p872 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked872 : lratChecker f872 p872 = .success := by decide +kernel
theorem unsat872 : Unsatisfiable (PosFin 57) f872 := by
  apply lratCheckerSound f872 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p872
  · intro a ha; simp [p872] at ha; subst a; trivial
  · exact checked872
theorem derived872 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c872 := by
  apply localUnsat_implies_entails f872 [c863, c842, c818, c871, c659, c870, c364, c336, c30, c382, c392, c396, c105, c121, c107, c81, c367, c355, c479, c690, c397, c124, c106] c872 unsat872 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c871 := derived871 a h
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c870 := derived870 a h
  have h6 : Entails.eval a c364 := h 363 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c392 := h 391 (by decide)
  have h11 : Entails.eval a c396 := h 395 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c367 := h 366 (by decide)
  have h17 : Entails.eval a c355 := h 354 (by decide)
  have h18 : Entails.eval a c479 := derived479 a h
  have h19 : Entails.eval a c690 := derived690 a h
  have h20 : Entails.eval a c397 := h 396 (by decide)
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c873 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨47, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f873 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c85, some c818, some c364, some c72, some c52, some c659, some c392, some c263, some c382, some c32, some c388, some c309, some c93, some c22, some c121, some c95, some c81, some c347, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p873 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked873 : lratChecker f873 p873 = .success := by decide +kernel
theorem unsat873 : Unsatisfiable (PosFin 57) f873 := by
  apply lratCheckerSound f873 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p873
  · intro a ha; simp [p873] at ha; subst a; trivial
  · exact checked873
theorem derived873 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c873 := by
  apply localUnsat_implies_entails f873 [c25, c85, c818, c364, c72, c52, c659, c392, c263, c382, c32, c388, c309, c93, c22, c121, c95, c81, c347] c873 unsat873 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c364 := h 363 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c659 := derived659 a h
  have h7 : Entails.eval a c392 := h 391 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c874 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨38, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true), (⟨47, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f874 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c392, some c263, some c382, some c362, some c24, some c32, some c868, some c309, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p874 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked874 : lratChecker f874 p874 = .success := by decide +kernel
theorem unsat874 : Unsatisfiable (PosFin 57) f874 := by
  apply lratCheckerSound f874 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p874
  · intro a ha; simp [p874] at ha; subst a; trivial
  · exact checked874
theorem derived874 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c874 := by
  apply localUnsat_implies_entails f874 [c659, c392, c263, c382, c362, c24, c32, c868, c309] c874 unsat874 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c392 := h 391 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c868 := derived868 a h
  have h8 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c875 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨39, by decide⟩, true), (⟨48, by decide⟩, false), (⟨38, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨47, by decide⟩, true), (⟨14, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f875 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c85, some c70, some c362, some c262, some c259, some c388, some c824, some c93, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p875 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked875 : lratChecker f875 p875 = .success := by decide +kernel
theorem unsat875 : Unsatisfiable (PosFin 57) f875 := by
  apply lratCheckerSound f875 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p875
  · intro a ha; simp [p875] at ha; subst a; trivial
  · exact checked875
theorem derived875 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c875 := by
  apply localUnsat_implies_entails f875 [c25, c85, c70, c362, c262, c259, c388, c824, c93] c875 unsat875 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c824 := derived824 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c876 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨9, by decide⟩, true), (⟨32, by decide⟩, false), (⟨48, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f876 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c309, some c93, some c184, some c22, some c7, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p876 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked876 : lratChecker f876 p876 = .success := by decide +kernel
theorem unsat876 : Unsatisfiable (PosFin 57) f876 := by
  apply lratCheckerSound f876 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p876
  · intro a ha; simp [p876] at ha; subst a; trivial
  · exact checked876
theorem derived876 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c876 := by
  apply localUnsat_implies_entails f876 [c388, c309, c93, c184, c22, c7] c876 unsat876 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c877 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f877 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c863, some c842, some c818, some c872, some c85, some c25, some c873, some c874, some c72, some c92, some c365, some c235, some c24, some c875, some c197, some c876, some c30, some c259, some c276, some c731, some c257, some c124, some c94, some c389, some c95, some c186, some c13, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p877 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked877 : lratChecker f877 p877 = .success := by decide +kernel
theorem unsat877 : Unsatisfiable (PosFin 57) f877 := by
  apply lratCheckerSound f877 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p877
  · intro a ha; simp [p877] at ha; subst a; trivial
  · exact checked877
theorem derived877 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c877 := by
  apply localUnsat_implies_entails f877 [c863, c842, c818, c872, c85, c25, c873, c874, c72, c92, c365, c235, c24, c875, c197, c876, c30, c259, c276, c731, c257, c124, c94, c389, c95, c186, c13] c877 unsat877 (by rfl) a
  have h0 : Entails.eval a c863 := derived863 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c872 := derived872 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c873 := derived873 a h
  have h7 : Entails.eval a c874 := derived874 a h
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c365 := h 364 (by decide)
  have h11 : Entails.eval a c235 := h 234 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c875 := derived875 a h
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c876 := derived876 a h
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c259 := h 258 (by decide)
  have h18 : Entails.eval a c276 := h 275 (by decide)
  have h19 : Entails.eval a c731 := derived731 a h
  have h20 : Entails.eval a c257 := h 256 (by decide)
  have h21 : Entails.eval a c124 := h 123 (by decide)
  have h22 : Entails.eval a c94 := h 93 (by decide)
  have h23 : Entails.eval a c389 := h 388 (by decide)
  have h24 : Entails.eval a c95 := h 94 (by decide)
  have h25 : Entails.eval a c186 := h 185 (by decide)
  have h26 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c878 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f878 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c877, some c117, some c690, some c863, some c72, some c92, some c115, some c364, some c736, some c133, some c731, some c235, some c259, some c24, some c43, some c388, some c309, some c260, some c371, some c252, some c184, some c294, some c216, some c217, some c329, some c186, some c149, some c163, some c535, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p878 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked878 : lratChecker f878 p878 = .success := by decide +kernel
theorem unsat878 : Unsatisfiable (PosFin 57) f878 := by
  apply lratCheckerSound f878 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p878
  · intro a ha; simp [p878] at ha; subst a; trivial
  · exact checked878
theorem derived878 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c878 := by
  apply localUnsat_implies_entails f878 [c818, c842, c877, c117, c690, c863, c72, c92, c115, c364, c736, c133, c731, c235, c259, c24, c43, c388, c309, c260, c371, c252, c184, c294, c216, c217, c329, c186, c149, c163, c535] c878 unsat878 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c877 := derived877 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c690 := derived690 a h
  have h5 : Entails.eval a c863 := derived863 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c364 := h 363 (by decide)
  have h10 : Entails.eval a c736 := derived736 a h
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c731 := derived731 a h
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c259 := h 258 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c388 := h 387 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  have h19 : Entails.eval a c260 := h 259 (by decide)
  have h20 : Entails.eval a c371 := h 370 (by decide)
  have h21 : Entails.eval a c252 := h 251 (by decide)
  have h22 : Entails.eval a c184 := h 183 (by decide)
  have h23 : Entails.eval a c294 := h 293 (by decide)
  have h24 : Entails.eval a c216 := h 215 (by decide)
  have h25 : Entails.eval a c217 := h 216 (by decide)
  have h26 : Entails.eval a c329 := h 328 (by decide)
  have h27 : Entails.eval a c186 := h 185 (by decide)
  have h28 : Entails.eval a c149 := h 148 (by decide)
  have h29 : Entails.eval a c163 := h 162 (by decide)
  have h30 : Entails.eval a c535 := derived535 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c879 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f879 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c842, some c818, some c877, some c117, some c690, some c707, some c659, some c736, some c388, some c507, some c184, some c396, some c216, some c362, some c186, some c364, some c347, some c180, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p879 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked879 : lratChecker f879 p879 = .success := by decide +kernel
theorem unsat879 : Unsatisfiable (PosFin 57) f879 := by
  apply lratCheckerSound f879 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p879
  · intro a ha; simp [p879] at ha; subst a; trivial
  · exact checked879
theorem derived879 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c879 := by
  apply localUnsat_implies_entails f879 [c878, c842, c818, c877, c117, c690, c707, c659, c736, c388, c507, c184, c396, c216, c362, c186, c364, c347, c180] c879 unsat879 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c877 := derived877 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c690 := derived690 a h
  have h6 : Entails.eval a c707 := derived707 a h
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c736 := derived736 a h
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c507 := derived507 a h
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c396 := h 395 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c362 := h 361 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c364 := h 363 (by decide)
  have h17 : Entails.eval a c347 := h 346 (by decide)
  have h18 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c880 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨48, by decide⟩, true), (⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f880 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c842, some c877, some c117, some c103, some c32, some c863, some c818, some c133, some c731, some c235, some c139, some c83, some c727, some c232, some c389, some c42, some c610, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p880 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked880 : lratChecker f880 p880 = .success := by decide +kernel
theorem unsat880 : Unsatisfiable (PosFin 57) f880 := by
  apply lratCheckerSound f880 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p880
  · intro a ha; simp [p880] at ha; subst a; trivial
  · exact checked880
theorem derived880 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c880 := by
  apply localUnsat_implies_entails f880 [c842, c877, c117, c103, c32, c863, c818, c133, c731, c235, c139, c83, c727, c232, c389, c42, c610] c880 unsat880 (by rfl) a
  have h0 : Entails.eval a c842 := derived842 a h
  have h1 : Entails.eval a c877 := derived877 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c863 := derived863 a h
  have h6 : Entails.eval a c818 := derived818 a h
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c731 := derived731 a h
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c139 := h 138 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c727 := derived727 a h
  have h13 : Entails.eval a c232 := h 231 (by decide)
  have h14 : Entails.eval a c389 := h 388 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c610 := derived610 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c881 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f881 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c878, some c842, some c818, some c877, some c117, some c690, some c707, some c863, some c879, some c32, some c103, some c880, some c2, some c712, some c3, some c42, some c700, some c139, some c283, some c278, some c249, some c755, some c389, some c267, some c101, some c250, some c373, some c750, some c271, some c472, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p881 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked881 : lratChecker f881 p881 = .success := by decide +kernel
theorem unsat881 : Unsatisfiable (PosFin 57) f881 := by
  apply lratCheckerSound f881 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p881
  · intro a ha; simp [p881] at ha; subst a; trivial
  · exact checked881
theorem derived881 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c881 := by
  apply localUnsat_implies_entails f881 [c878, c842, c818, c877, c117, c690, c707, c863, c879, c32, c103, c880, c2, c712, c3, c42, c700, c139, c283, c278, c249, c755, c389, c267, c101, c250, c373, c750, c271, c472] c881 unsat881 (by rfl) a
  have h0 : Entails.eval a c878 := derived878 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c877 := derived877 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c690 := derived690 a h
  have h6 : Entails.eval a c707 := derived707 a h
  have h7 : Entails.eval a c863 := derived863 a h
  have h8 : Entails.eval a c879 := derived879 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c880 := derived880 a h
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c712 := derived712 a h
  have h14 : Entails.eval a c3 := h 2 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c700 := derived700 a h
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c283 := h 282 (by decide)
  have h19 : Entails.eval a c278 := h 277 (by decide)
  have h20 : Entails.eval a c249 := h 248 (by decide)
  have h21 : Entails.eval a c755 := derived755 a h
  have h22 : Entails.eval a c389 := h 388 (by decide)
  have h23 : Entails.eval a c267 := h 266 (by decide)
  have h24 : Entails.eval a c101 := h 100 (by decide)
  have h25 : Entails.eval a c250 := h 249 (by decide)
  have h26 : Entails.eval a c373 := h 372 (by decide)
  have h27 : Entails.eval a c750 := derived750 a h
  have h28 : Entails.eval a c271 := h 270 (by decide)
  have h29 : Entails.eval a c472 := derived472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c882 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f882 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c842, some c877, some c117, some c863, some c259, some c735, some c731, some c133, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p882 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked882 : lratChecker f882 p882 = .success := by decide +kernel
theorem unsat882 : Unsatisfiable (PosFin 57) f882 := by
  apply lratCheckerSound f882 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p882
  · intro a ha; simp [p882] at ha; subst a; trivial
  · exact checked882
theorem derived882 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c882 := by
  apply localUnsat_implies_entails f882 [c842, c877, c117, c863, c259, c735, c731, c133] c882 unsat882 (by rfl) a
  have h0 : Entails.eval a c842 := derived842 a h
  have h1 : Entails.eval a c877 := derived877 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c863 := derived863 a h
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c735 := derived735 a h
  have h6 : Entails.eval a c731 := derived731 a h
  have h7 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c883 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨25, by decide⟩, true), (⟨37, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f883 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c638, some c263, some c43, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p883 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked883 : lratChecker f883 p883 = .success := by decide +kernel
theorem unsat883 : Unsatisfiable (PosFin 57) f883 := by
  apply lratCheckerSound f883 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p883
  · intro a ha; simp [p883] at ha; subst a; trivial
  · exact checked883
theorem derived883 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c883 := by
  apply localUnsat_implies_entails f883 [c133, c638, c263, c43] c883 unsat883 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c884 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f884 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c877, some c117, some c690, some c863, some c878, some c659, some c882, some c881, some c392, some c362, some c364, some c52, some c83, some c314, some c883, some c2, some c736, some c3, some c757, some c42, some c32, some c139, some c332, some c276, some c220, some c267, some c375, some c355, some c341, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p884 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked884 : lratChecker f884 p884 = .success := by decide +kernel
theorem unsat884 : Unsatisfiable (PosFin 57) f884 := by
  apply lratCheckerSound f884 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p884
  · intro a ha; simp [p884] at ha; subst a; trivial
  · exact checked884
theorem derived884 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c884 := by
  apply localUnsat_implies_entails f884 [c818, c842, c877, c117, c690, c863, c878, c659, c882, c881, c392, c362, c364, c52, c83, c314, c883, c2, c736, c3, c757, c42, c32, c139, c332, c276, c220, c267, c375, c355, c341] c884 unsat884 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c877 := derived877 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c690 := derived690 a h
  have h5 : Entails.eval a c863 := derived863 a h
  have h6 : Entails.eval a c878 := derived878 a h
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c882 := derived882 a h
  have h9 : Entails.eval a c881 := derived881 a h
  have h10 : Entails.eval a c392 := h 391 (by decide)
  have h11 : Entails.eval a c362 := h 361 (by decide)
  have h12 : Entails.eval a c364 := h 363 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c883 := derived883 a h
  have h17 : Entails.eval a c2 := h 1 (by decide)
  have h18 : Entails.eval a c736 := derived736 a h
  have h19 : Entails.eval a c3 := h 2 (by decide)
  have h20 : Entails.eval a c757 := derived757 a h
  have h21 : Entails.eval a c42 := h 41 (by decide)
  have h22 : Entails.eval a c32 := h 31 (by decide)
  have h23 : Entails.eval a c139 := h 138 (by decide)
  have h24 : Entails.eval a c332 := h 331 (by decide)
  have h25 : Entails.eval a c276 := h 275 (by decide)
  have h26 : Entails.eval a c220 := h 219 (by decide)
  have h27 : Entails.eval a c267 := h 266 (by decide)
  have h28 : Entails.eval a c375 := h 374 (by decide)
  have h29 : Entails.eval a c355 := h 354 (by decide)
  have h30 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c885 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨41, by decide⟩, false), (⟨39, by decide⟩, true), (⟨47, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f885 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c362, some c382, some c336, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p885 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked885 : lratChecker f885 p885 = .success := by decide +kernel
theorem unsat885 : Unsatisfiable (PosFin 57) f885 := by
  apply lratCheckerSound f885 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p885
  · intro a ha; simp [p885] at ha; subst a; trivial
  · exact checked885
theorem derived885 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c885 := by
  apply localUnsat_implies_entails f885 [c362, c382, c336] c885 unsat885 (by rfl) a
  have h0 : Entails.eval a c362 := h 361 (by decide)
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c886 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, false), (⟨47, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f886 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c396, some c375, some c384, some c387, some c378, some c409, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p886 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked886 : lratChecker f886 p886 = .success := by decide +kernel
theorem unsat886 : Unsatisfiable (PosFin 57) f886 := by
  apply lratCheckerSound f886 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p886
  · intro a ha; simp [p886] at ha; subst a; trivial
  · exact checked886
theorem derived886 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c886 := by
  apply localUnsat_implies_entails f886 [c659, c396, c375, c384, c387, c378, c409] c886 unsat886 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c396 := h 395 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c387 := h 386 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c409 := derived409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c887 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f887 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c842, some c818, some c863, some c877, some c117, some c690, some c884, some c871, some c659, some c885, some c886, some c259, some c735, some c731, some c683, some c686, some c103, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p887 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked887 : lratChecker f887 p887 = .success := by decide +kernel
theorem unsat887 : Unsatisfiable (PosFin 57) f887 := by
  apply lratCheckerSound f887 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p887
  · intro a ha; simp [p887] at ha; subst a; trivial
  · exact checked887
theorem derived887 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c887 := by
  apply localUnsat_implies_entails f887 [c842, c818, c863, c877, c117, c690, c884, c871, c659, c885, c886, c259, c735, c731, c683, c686, c103] c887 unsat887 (by rfl) a
  have h0 : Entails.eval a c842 := derived842 a h
  have h1 : Entails.eval a c818 := derived818 a h
  have h2 : Entails.eval a c863 := derived863 a h
  have h3 : Entails.eval a c877 := derived877 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c690 := derived690 a h
  have h6 : Entails.eval a c884 := derived884 a h
  have h7 : Entails.eval a c871 := derived871 a h
  have h8 : Entails.eval a c659 := derived659 a h
  have h9 : Entails.eval a c885 := derived885 a h
  have h10 : Entails.eval a c886 := derived886 a h
  have h11 : Entails.eval a c259 := h 258 (by decide)
  have h12 : Entails.eval a c735 := derived735 a h
  have h13 : Entails.eval a c731 := derived731 a h
  have h14 : Entails.eval a c683 := derived683 a h
  have h15 : Entails.eval a c686 := derived686 a h
  have h16 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c888 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f888 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c32, some c117, some c690, some c103, some c183, some c335, some c3, some c83, some c125, some c235, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p888 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked888 : lratChecker f888 p888 = .success := by decide +kernel
theorem unsat888 : Unsatisfiable (PosFin 57) f888 := by
  apply lratCheckerSound f888 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p888
  · intro a ha; simp [p888] at ha; subst a; trivial
  · exact checked888
theorem derived888 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c888 := by
  apply localUnsat_implies_entails f888 [c32, c117, c690, c103, c183, c335, c3, c83, c125, c235] c888 unsat888 (by rfl) a
  have h0 : Entails.eval a c32 := h 31 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c690 := derived690 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c335 := h 334 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c889 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f889 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c887, some c138, some c130, some c842, some c818, some c871, some c296, some c384, some c336, some c659, some c32, some c888, some c864, some c866, some c865, some c843, some c362, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p889 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked889 : lratChecker f889 p889 = .success := by decide +kernel
theorem unsat889 : Unsatisfiable (PosFin 57) f889 := by
  apply lratCheckerSound f889 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p889
  · intro a ha; simp [p889] at ha; subst a; trivial
  · exact checked889
theorem derived889 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c889 := by
  apply localUnsat_implies_entails f889 [c887, c138, c130, c842, c818, c871, c296, c384, c336, c659, c32, c888, c864, c866, c865, c843, c362] c889 unsat889 (by rfl) a
  have h0 : Entails.eval a c887 := derived887 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c842 := derived842 a h
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c871 := derived871 a h
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c336 := h 335 (by decide)
  have h9 : Entails.eval a c659 := derived659 a h
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c888 := derived888 a h
  have h12 : Entails.eval a c864 := derived864 a h
  have h13 : Entails.eval a c866 := derived866 a h
  have h14 : Entails.eval a c865 := derived865 a h
  have h15 : Entails.eval a c843 := derived843 a h
  have h16 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c890 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f890 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c25, some c263, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false))]
def p890 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked890 : lratChecker f890 p890 = .success := by decide +kernel
theorem unsat890 : Unsatisfiable (PosFin 57) f890 := by
  apply lratCheckerSound f890 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p890
  · intro a ha; simp [p890] at ha; subst a; trivial
  · exact checked890
theorem derived890 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c890 := by
  apply localUnsat_implies_entails f890 [c85, c25, c263] c890 unsat890 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c891 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f891 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c727, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p891 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked891 : lratChecker f891 p891 = .success := by decide +kernel
theorem unsat891 : Unsatisfiable (PosFin 57) f891 := by
  apply lratCheckerSound f891 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p891
  · intro a ha; simp [p891] at ha; subst a; trivial
  · exact checked891
theorem derived891 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c891 := by
  apply localUnsat_implies_entails f891 [c3, c727] c891 unsat891 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c727 := derived727 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c892 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨47, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f892 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c843, some c889, some c887, some c32, some c890, some c117, some c103, some c390, some c891, some c152, some c159, some c731, some c308, some c249, some c21, some c283, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p892 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked892 : lratChecker f892 p892 = .success := by decide +kernel
theorem unsat892 : Unsatisfiable (PosFin 57) f892 := by
  apply lratCheckerSound f892 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p892
  · intro a ha; simp [p892] at ha; subst a; trivial
  · exact checked892
theorem derived892 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c892 := by
  apply localUnsat_implies_entails f892 [c818, c842, c843, c889, c887, c32, c890, c117, c103, c390, c891, c152, c159, c731, c308, c249, c21, c283] c892 unsat892 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c843 := derived843 a h
  have h3 : Entails.eval a c889 := derived889 a h
  have h4 : Entails.eval a c887 := derived887 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c890 := derived890 a h
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c390 := h 389 (by decide)
  have h10 : Entails.eval a c891 := derived891 a h
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c731 := derived731 a h
  have h14 : Entails.eval a c308 := h 307 (by decide)
  have h15 : Entails.eval a c249 := h 248 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c893 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f893 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c889, some c887, some c138, some c130, some c842, some c818, some c843, some c892, some c309, some c24, some c52, some c890, some c364, some c235, some c183, some c621, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p893 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked893 : lratChecker f893 p893 = .success := by decide +kernel
theorem unsat893 : Unsatisfiable (PosFin 57) f893 := by
  apply lratCheckerSound f893 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p893
  · intro a ha; simp [p893] at ha; subst a; trivial
  · exact checked893
theorem derived893 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c893 := by
  apply localUnsat_implies_entails f893 [c889, c887, c138, c130, c842, c818, c843, c892, c309, c24, c52, c890, c364, c235, c183, c621] c893 unsat893 (by rfl) a
  have h0 : Entails.eval a c889 := derived889 a h
  have h1 : Entails.eval a c887 := derived887 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c842 := derived842 a h
  have h5 : Entails.eval a c818 := derived818 a h
  have h6 : Entails.eval a c843 := derived843 a h
  have h7 : Entails.eval a c892 := derived892 a h
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c890 := derived890 a h
  have h12 : Entails.eval a c364 := h 363 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c183 := h 182 (by decide)
  have h15 : Entails.eval a c621 := derived621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c894 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨47, by decide⟩, true), (⟨56, by decide⟩, false), (⟨46, by decide⟩, false), (⟨30, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f894 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c388, some c309, some c375, some c52, some c396, some c365, some c364, some c362, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p894 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked894 : lratChecker f894 p894 = .success := by decide +kernel
theorem unsat894 : Unsatisfiable (PosFin 57) f894 := by
  apply lratCheckerSound f894 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p894
  · intro a ha; simp [p894] at ha; subst a; trivial
  · exact checked894
theorem derived894 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c894 := by
  apply localUnsat_implies_entails f894 [c659, c388, c309, c375, c52, c396, c365, c364, c362] c894 unsat894 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c396 := h 395 (by decide)
  have h6 : Entails.eval a c365 := h 364 (by decide)
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c895 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨7, by decide⟩, false), (⟨33, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f895 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c890, some c117, some c690, some c659, some c183, some c362, some c3, some c325, some c133, some c52, some c235, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p895 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked895 : lratChecker f895 p895 = .success := by decide +kernel
theorem unsat895 : Unsatisfiable (PosFin 57) f895 := by
  apply lratCheckerSound f895 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p895
  · intro a ha; simp [p895] at ha; subst a; trivial
  · exact checked895
theorem derived895 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c895 := by
  apply localUnsat_implies_entails f895 [c890, c117, c690, c659, c183, c362, c3, c325, c133, c52, c235] c895 unsat895 (by rfl) a
  have h0 : Entails.eval a c890 := derived890 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c690 := derived690 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c362 := h 361 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c896 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f896 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c887, some c130, some c818, some c842, some c889, some c138, some c893, some c894, some c32, some c895, some c364, some c52, some c328, some c890, some c117, some c83, some c103, some c731, some c232, some c139, some c21, some c150, some c3, some c891, some c304, some c219, some c162, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p896 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked896 : lratChecker f896 p896 = .success := by decide +kernel
theorem unsat896 : Unsatisfiable (PosFin 57) f896 := by
  apply lratCheckerSound f896 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p896
  · intro a ha; simp [p896] at ha; subst a; trivial
  · exact checked896
theorem derived896 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c896 := by
  apply localUnsat_implies_entails f896 [c887, c130, c818, c842, c889, c138, c893, c894, c32, c895, c364, c52, c328, c890, c117, c83, c103, c731, c232, c139, c21, c150, c3, c891, c304, c219, c162] c896 unsat896 (by rfl) a
  have h0 : Entails.eval a c887 := derived887 a h
  have h1 : Entails.eval a c130 := h 129 (by decide)
  have h2 : Entails.eval a c818 := derived818 a h
  have h3 : Entails.eval a c842 := derived842 a h
  have h4 : Entails.eval a c889 := derived889 a h
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c893 := derived893 a h
  have h7 : Entails.eval a c894 := derived894 a h
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c895 := derived895 a h
  have h10 : Entails.eval a c364 := h 363 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c890 := derived890 a h
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c103 := h 102 (by decide)
  have h17 : Entails.eval a c731 := derived731 a h
  have h18 : Entails.eval a c232 := h 231 (by decide)
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c150 := h 149 (by decide)
  have h22 : Entails.eval a c3 := h 2 (by decide)
  have h23 : Entails.eval a c891 := derived891 a h
  have h24 : Entails.eval a c304 := h 303 (by decide)
  have h25 : Entails.eval a c219 := h 218 (by decide)
  have h26 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c897 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f897 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c889, some c887, some c138, some c130, some c842, some c818, some c659, some c893, some c894, some c32, some c890, some c117, some c690, some c895, some c364, some c52, some c328, some c332, some c896, some c220, some c267, some c375, some c355, some c341, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p897 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked897 : lratChecker f897 p897 = .success := by decide +kernel
theorem unsat897 : Unsatisfiable (PosFin 57) f897 := by
  apply lratCheckerSound f897 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p897
  · intro a ha; simp [p897] at ha; subst a; trivial
  · exact checked897
theorem derived897 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c897 := by
  apply localUnsat_implies_entails f897 [c889, c887, c138, c130, c842, c818, c659, c893, c894, c32, c890, c117, c690, c895, c364, c52, c328, c332, c896, c220, c267, c375, c355, c341] c897 unsat897 (by rfl) a
  have h0 : Entails.eval a c889 := derived889 a h
  have h1 : Entails.eval a c887 := derived887 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c842 := derived842 a h
  have h5 : Entails.eval a c818 := derived818 a h
  have h6 : Entails.eval a c659 := derived659 a h
  have h7 : Entails.eval a c893 := derived893 a h
  have h8 : Entails.eval a c894 := derived894 a h
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c890 := derived890 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c690 := derived690 a h
  have h13 : Entails.eval a c895 := derived895 a h
  have h14 : Entails.eval a c364 := h 363 (by decide)
  have h15 : Entails.eval a c52 := h 51 (by decide)
  have h16 : Entails.eval a c328 := h 327 (by decide)
  have h17 : Entails.eval a c332 := h 331 (by decide)
  have h18 : Entails.eval a c896 := derived896 a h
  have h19 : Entails.eval a c220 := h 219 (by decide)
  have h20 : Entails.eval a c267 := h 266 (by decide)
  have h21 : Entails.eval a c375 := h 374 (by decide)
  have h22 : Entails.eval a c355 := h 354 (by decide)
  have h23 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c898 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f898 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c818, some c842, some c887, some c130, some c138, some c889, some c897, some c72, some c92, some c365, some c364, some c309, some c183, some c24, some c235, some c25, some c621, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p898 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked898 : lratChecker f898 p898 = .success := by decide +kernel
theorem unsat898 : Unsatisfiable (PosFin 57) f898 := by
  apply lratCheckerSound f898 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p898
  · intro a ha; simp [p898] at ha; subst a; trivial
  · exact checked898
theorem derived898 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c898 := by
  apply localUnsat_implies_entails f898 [c818, c842, c887, c130, c138, c889, c897, c72, c92, c365, c364, c309, c183, c24, c235, c25, c621] c898 unsat898 (by rfl) a
  have h0 : Entails.eval a c818 := derived818 a h
  have h1 : Entails.eval a c842 := derived842 a h
  have h2 : Entails.eval a c887 := derived887 a h
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c889 := derived889 a h
  have h6 : Entails.eval a c897 := derived897 a h
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c364 := h 363 (by decide)
  have h11 : Entails.eval a c309 := h 308 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c621 := derived621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived898

end CochromaticTwenty.Certificates.B16_3_2
