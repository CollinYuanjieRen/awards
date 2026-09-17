import MerLeanExperiment.Certificates.Z12Direct_4_4_8.Steps0000_0099

/-! Generated from the actual pinned z12direct_4_4_8-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_4_8
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c346 : DefaultClause 29 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f346 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c345, some c334, some c315, some c137, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p346 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked346 : lratChecker f346 p346 = .success := by decide +kernel
theorem unsat346 : Unsatisfiable (PosFin 29) f346 := by
  apply lratCheckerSound f346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p346
  · intro a ha; simp [p346] at ha; subst a; trivial
  · exact checked346
theorem derived346 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c346 := by
  apply localUnsat_implies_entails f346 [c345, c334, c315, c137] c346 unsat346 (by rfl) a
  have h0 : Entails.eval a c345 := derived345 a h
  have h1 : Entails.eval a c334 := derived334 a h
  have h2 : Entails.eval a c315 := derived315 a h
  have h3 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c347 : DefaultClause 29 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f347 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c346, some c43, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p347 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked347 : lratChecker f347 p347 = .success := by decide +kernel
theorem unsat347 : Unsatisfiable (PosFin 29) f347 := by
  apply lratCheckerSound f347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p347
  · intro a ha; simp [p347] at ha; subst a; trivial
  · exact checked347
theorem derived347 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c347 := by
  apply localUnsat_implies_entails f347 [c346, c43] c347 unsat347 (by rfl) a
  have h0 : Entails.eval a c346 := derived346 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c348 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f348 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c347, some c334, some c345, some c142, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p348 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked348 : lratChecker f348 p348 = .success := by decide +kernel
theorem unsat348 : Unsatisfiable (PosFin 29) f348 := by
  apply lratCheckerSound f348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p348
  · intro a ha; simp [p348] at ha; subst a; trivial
  · exact checked348
theorem derived348 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c348 := by
  apply localUnsat_implies_entails f348 [c347, c334, c345, c142] c348 unsat348 (by rfl) a
  have h0 : Entails.eval a c347 := derived347 a h
  have h1 : Entails.eval a c334 := derived334 a h
  have h2 : Entails.eval a c345 := derived345 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c349 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f349 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c348, some c346, some c36, some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p349 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked349 : lratChecker f349 p349 = .success := by decide +kernel
theorem unsat349 : Unsatisfiable (PosFin 29) f349 := by
  apply lratCheckerSound f349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p349
  · intro a ha; simp [p349] at ha; subst a; trivial
  · exact checked349
theorem derived349 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c349 := by
  apply localUnsat_implies_entails f349 [c348, c346, c36] c349 unsat349 (by rfl) a
  have h0 : Entails.eval a c348 := derived348 a h
  have h1 : Entails.eval a c346 := derived346 a h
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c350 : DefaultClause 29 := directClause [(⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f350 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c347, some c334, some c345, some c182, some c219, some c16, some c31, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p350 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked350 : lratChecker f350 p350 = .success := by decide +kernel
theorem unsat350 : Unsatisfiable (PosFin 29) f350 := by
  apply lratCheckerSound f350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p350
  · intro a ha; simp [p350] at ha; subst a; trivial
  · exact checked350
theorem derived350 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c350 := by
  apply localUnsat_implies_entails f350 [c347, c334, c345, c182, c219, c16, c31] c350 unsat350 (by rfl) a
  have h0 : Entails.eval a c347 := derived347 a h
  have h1 : Entails.eval a c334 := derived334 a h
  have h2 : Entails.eval a c345 := derived345 a h
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c351 : DefaultClause 29 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f351 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c346, some c348, some c334, some c315, some c350, some c44, some c56, some c227, some c186, some c55, some c150, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p351 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked351 : lratChecker f351 p351 = .success := by decide +kernel
theorem unsat351 : Unsatisfiable (PosFin 29) f351 := by
  apply lratCheckerSound f351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p351
  · intro a ha; simp [p351] at ha; subst a; trivial
  · exact checked351
theorem derived351 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c351 := by
  apply localUnsat_implies_entails f351 [c346, c348, c334, c315, c350, c44, c56, c227, c186, c55, c150] c351 unsat351 (by rfl) a
  have h0 : Entails.eval a c346 := derived346 a h
  have h1 : Entails.eval a c348 := derived348 a h
  have h2 : Entails.eval a c334 := derived334 a h
  have h3 : Entails.eval a c315 := derived315 a h
  have h4 : Entails.eval a c350 := derived350 a h
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c352 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f352 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c333, some c344, some c349, some c334, some c347, some c345, some c351, some c42, some c5, some c66, some c76, some c63, some c199, some c181, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p352 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked352 : lratChecker f352 p352 = .success := by decide +kernel
theorem unsat352 : Unsatisfiable (PosFin 29) f352 := by
  apply lratCheckerSound f352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p352
  · intro a ha; simp [p352] at ha; subst a; trivial
  · exact checked352
theorem derived352 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c352 := by
  apply localUnsat_implies_entails f352 [c333, c344, c349, c334, c347, c345, c351, c42, c5, c66, c76, c63, c199, c181] c352 unsat352 (by rfl) a
  have h0 : Entails.eval a c333 := derived333 a h
  have h1 : Entails.eval a c344 := derived344 a h
  have h2 : Entails.eval a c349 := derived349 a h
  have h3 : Entails.eval a c334 := derived334 a h
  have h4 : Entails.eval a c347 := derived347 a h
  have h5 : Entails.eval a c345 := derived345 a h
  have h6 : Entails.eval a c351 := derived351 a h
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c353 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f353 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c352, some c61, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p353 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked353 : lratChecker f353 p353 = .success := by decide +kernel
theorem unsat353 : Unsatisfiable (PosFin 29) f353 := by
  apply lratCheckerSound f353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p353
  · intro a ha; simp [p353] at ha; subst a; trivial
  · exact checked353
theorem derived353 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c353 := by
  apply localUnsat_implies_entails f353 [c352, c61] c353 unsat353 (by rfl) a
  have h0 : Entails.eval a c352 := derived352 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c354 : DefaultClause 29 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f354 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c353, some c334, some c347, some c5, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p354 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked354 : lratChecker f354 p354 = .success := by decide +kernel
theorem unsat354 : Unsatisfiable (PosFin 29) f354 := by
  apply lratCheckerSound f354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p354
  · intro a ha; simp [p354] at ha; subst a; trivial
  · exact checked354
theorem derived354 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c354 := by
  apply localUnsat_implies_entails f354 [c353, c334, c347, c5] c354 unsat354 (by rfl) a
  have h0 : Entails.eval a c353 := derived353 a h
  have h1 : Entails.eval a c334 := derived334 a h
  have h2 : Entails.eval a c347 := derived347 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c355 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f355 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c354, some c42, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p355 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked355 : lratChecker f355 p355 = .success := by decide +kernel
theorem unsat355 : Unsatisfiable (PosFin 29) f355 := by
  apply lratCheckerSound f355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p355
  · intro a ha; simp [p355] at ha; subst a; trivial
  · exact checked355
theorem derived355 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c355 := by
  apply localUnsat_implies_entails f355 [c354, c42] c355 unsat355 (by rfl) a
  have h0 : Entails.eval a c354 := derived354 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c356 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f356 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c354, some c346, some c348, some c55, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p356 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked356 : lratChecker f356 p356 = .success := by decide +kernel
theorem unsat356 : Unsatisfiable (PosFin 29) f356 := by
  apply lratCheckerSound f356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p356
  · intro a ha; simp [p356] at ha; subst a; trivial
  · exact checked356
theorem derived356 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c356 := by
  apply localUnsat_implies_entails f356 [c354, c346, c348, c55] c356 unsat356 (by rfl) a
  have h0 : Entails.eval a c354 := derived354 a h
  have h1 : Entails.eval a c346 := derived346 a h
  have h2 : Entails.eval a c348 := derived348 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c357 : DefaultClause 29 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f357 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c356, some c346, some c348, some c56, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p357 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked357 : lratChecker f357 p357 = .success := by decide +kernel
theorem unsat357 : Unsatisfiable (PosFin 29) f357 := by
  apply lratCheckerSound f357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p357
  · intro a ha; simp [p357] at ha; subst a; trivial
  · exact checked357
theorem derived357 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c357 := by
  apply localUnsat_implies_entails f357 [c356, c346, c348, c56] c357 unsat357 (by rfl) a
  have h0 : Entails.eval a c356 := derived356 a h
  have h1 : Entails.eval a c346 := derived346 a h
  have h2 : Entails.eval a c348 := derived348 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c358 : DefaultClause 29 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f358 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c357, some c44, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p358 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked358 : lratChecker f358 p358 = .success := by decide +kernel
theorem unsat358 : Unsatisfiable (PosFin 29) f358 := by
  apply lratCheckerSound f358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p358
  · intro a ha; simp [p358] at ha; subst a; trivial
  · exact checked358
theorem derived358 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c358 := by
  apply localUnsat_implies_entails f358 [c357, c44] c358 unsat358 (by rfl) a
  have h0 : Entails.eval a c357 := derived357 a h
  have h1 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c359 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f359 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c358, some c355, some c334, some c345, some c347, some c182, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p359 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked359 : lratChecker f359 p359 = .success := by decide +kernel
theorem unsat359 : Unsatisfiable (PosFin 29) f359 := by
  apply lratCheckerSound f359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p359
  · intro a ha; simp [p359] at ha; subst a; trivial
  · exact checked359
theorem derived359 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c359 := by
  apply localUnsat_implies_entails f359 [c358, c355, c334, c345, c347, c182] c359 unsat359 (by rfl) a
  have h0 : Entails.eval a c358 := derived358 a h
  have h1 : Entails.eval a c355 := derived355 a h
  have h2 : Entails.eval a c334 := derived334 a h
  have h3 : Entails.eval a c345 := derived345 a h
  have h4 : Entails.eval a c347 := derived347 a h
  have h5 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c360 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f360 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c358, some c359, some c347, some c349, some c352, some c334, some c200]
def p360 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked360 : lratChecker f360 p360 = .success := by decide +kernel
theorem unsat360 : Unsatisfiable (PosFin 29) f360 := by
  apply lratCheckerSound f360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p360
  · intro a ha; simp [p360] at ha; subst a; trivial
  · exact checked360
theorem derived360 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c360 := by
  apply localUnsat_implies_entails f360 [c358, c359, c347, c349, c352, c334, c200] c360 unsat360 (by rfl) a
  have h0 : Entails.eval a c358 := derived358 a h
  have h1 : Entails.eval a c359 := derived359 a h
  have h2 : Entails.eval a c347 := derived347 a h
  have h3 : Entails.eval a c349 := derived349 a h
  have h4 : Entails.eval a c352 := derived352 a h
  have h5 : Entails.eval a c334 := derived334 a h
  have h6 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived360

end CochromaticTwenty.Certificates.Z12Direct_4_4_8
