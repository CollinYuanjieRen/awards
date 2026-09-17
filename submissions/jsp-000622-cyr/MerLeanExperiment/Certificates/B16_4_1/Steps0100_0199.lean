import MerLeanExperiment.Certificates.B16_4_1.Steps0000_0099

/-! Generated from the actual pinned b16_4_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c485 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c477, some c357, some c478, some c463, some c382, some c378, some c354, some c355, some c482, some c484, some c164, some c117, some c245, some c246, some c483, some c122, some c114, some c183, some c323, some c131, some c165, some c155, some c372, some c341, some c229, some c221, some c259, some c206, some c125, some c137, some c191, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 57) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c475, c477, c357, c478, c463, c382, c378, c354, c355, c482, c484, c164, c117, c245, c246, c483, c122, c114, c183, c323, c131, c165, c155, c372, c341, c229, c221, c259, c206, c125, c137, c191] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c477 := derived477 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c478 := derived478 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c482 := derived482 a h
  have h10 : Entails.eval a c484 := derived484 a h
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c483 := derived483 a h
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  have h18 : Entails.eval a c183 := h 182 (by decide)
  have h19 : Entails.eval a c323 := h 322 (by decide)
  have h20 : Entails.eval a c131 := h 130 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c155 := h 154 (by decide)
  have h23 : Entails.eval a c372 := h 371 (by decide)
  have h24 : Entails.eval a c341 := h 340 (by decide)
  have h25 : Entails.eval a c229 := h 228 (by decide)
  have h26 : Entails.eval a c221 := h 220 (by decide)
  have h27 : Entails.eval a c259 := h 258 (by decide)
  have h28 : Entails.eval a c206 := h 205 (by decide)
  have h29 : Entails.eval a c125 := h 124 (by decide)
  have h30 : Entails.eval a c137 := h 136 (by decide)
  have h31 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c486 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c485, some c475, some c477, some c357, some c478, some c135, some c117, some c245, some c246, some c483, some c122, some c114, some c183, some c312, some c131, some c165, some c155, some c470, some c367, some c341, some c229, some c25, some c253, some c4, some c19, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 57) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c485, c475, c477, c357, c478, c135, c117, c245, c246, c483, c122, c114, c183, c312, c131, c165, c155, c470, c367, c341, c229, c25, c253, c4, c19] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c485 := derived485 a h
  have h1 : Entails.eval a c475 := derived475 a h
  have h2 : Entails.eval a c477 := derived477 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c478 := derived478 a h
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c246 := h 245 (by decide)
  have h9 : Entails.eval a c483 := derived483 a h
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c131 := h 130 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c470 := derived470 a h
  have h18 : Entails.eval a c367 := h 366 (by decide)
  have h19 : Entails.eval a c341 := h 340 (by decide)
  have h20 : Entails.eval a c229 := h 228 (by decide)
  have h21 : Entails.eval a c25 := h 24 (by decide)
  have h22 : Entails.eval a c253 := h 252 (by decide)
  have h23 : Entails.eval a c4 := h 3 (by decide)
  have h24 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c487 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, false), (⟨41, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c121, some c113, some c254, some c311, some c19, some c107, some c1, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 57) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c132, c121, c113, c254, c311, c19, c107, c1] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c254 := h 253 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨33, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c107, some c1, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 57) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c19, c107, c1] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c477, some c357, some c478, some c485, some c486, some c178, some c483, some c227, some c21, some c487, some c250, some c228, some c218, some c367, some c341, some c310, some c166, some c139, some c488, some c254, some c199, some c131, some c133, some c186, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 57) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c475, c477, c357, c478, c485, c486, c178, c483, c227, c21, c487, c250, c228, c218, c367, c341, c310, c166, c139, c488, c254, c199, c131, c133, c186] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c477 := derived477 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c478 := derived478 a h
  have h4 : Entails.eval a c485 := derived485 a h
  have h5 : Entails.eval a c486 := derived486 a h
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c483 := derived483 a h
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c487 := derived487 a h
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c367 := h 366 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c166 := h 165 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c488 := derived488 a h
  have h20 : Entails.eval a c254 := h 253 (by decide)
  have h21 : Entails.eval a c199 := h 198 (by decide)
  have h22 : Entails.eval a c131 := h 130 (by decide)
  have h23 : Entails.eval a c133 := h 132 (by decide)
  have h24 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨39, by decide⟩, true), (⟨36, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c184, some c131, some c156, some c180, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 57) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c185, c184, c131, c156, c180] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c156 := h 155 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨38, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c341, some c338, some c180, some c183, some c156, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 57) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c341, c338, c180, c183, c156] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c341 := h 340 (by decide)
  have h1 : Entails.eval a c338 := h 337 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c183 := h 182 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c492 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨41, by decide⟩, false), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c21, some c247, some c248, some c218, some c338, some c341, some c490, some c491, some c131, some c120, some c181, some c310, some c136, some c488, some c133, some c197, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 57) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c21, c247, c248, c218, c338, c341, c490, c491, c131, c120, c181, c310, c136, c488, c133, c197] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c218 := h 217 (by decide)
  have h4 : Entails.eval a c338 := h 337 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c490 := derived490 a h
  have h7 : Entails.eval a c491 := derived491 a h
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c181 := h 180 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c488 := derived488 a h
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c217, some c180, some c181, some c338, some c339, some c159, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 57) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c118, c217, c180, c181, c338, c339, c159] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c181 := h 180 (by decide)
  have h4 : Entails.eval a c338 := h 337 (by decide)
  have h5 : Entails.eval a c339 := h 338 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c494 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f494 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c382, some c378, some c493, some c247, some c248, some c492, some c218, some c354, some c491, some c120, some c131, some c372, some c316, some c181, some c194, some c166, some c129, some c190, some c258, some c108, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p494 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked494 : lratChecker f494 p494 = .success := by decide +kernel
theorem unsat494 : Unsatisfiable (PosFin 57) f494 := by
  apply lratCheckerSound f494 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p494
  · intro a ha; simp [p494] at ha; subst a; trivial
  · exact checked494
theorem derived494 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c494 := by
  apply localUnsat_implies_entails f494 [c489, c382, c378, c493, c247, c248, c492, c218, c354, c491, c120, c131, c372, c316, c181, c194, c166, c129, c190, c258, c108] c494 unsat494 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c493 := derived493 a h
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c492 := derived492 a h
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c354 := h 353 (by decide)
  have h9 : Entails.eval a c491 := derived491 a h
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c129 := h 128 (by decide)
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c258 := h 257 (by decide)
  have h20 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c495 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨11, by decide⟩, false), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f495 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c338, some c181, some c194, some c118, some c156, some c247, some c190, some c120, some c129, some c258, some c116, some c108, some c316, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p495 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked495 : lratChecker f495 p495 = .success := by decide +kernel
theorem unsat495 : Unsatisfiable (PosFin 57) f495 := by
  apply lratCheckerSound f495 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p495
  · intro a ha; simp [p495] at ha; subst a; trivial
  · exact checked495
theorem derived495 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c495 := by
  apply localUnsat_implies_entails f495 [c338, c181, c194, c118, c156, c247, c190, c120, c129, c258, c116, c108, c316] c495 unsat495 (by rfl) a
  have h0 : Entails.eval a c338 := h 337 (by decide)
  have h1 : Entails.eval a c181 := h 180 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c129 := h 128 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c496 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f496 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c247, some c248, some c131, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p496 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked496 : lratChecker f496 p496 = .success := by decide +kernel
theorem unsat496 : Unsatisfiable (PosFin 57) f496 := by
  apply lratCheckerSound f496 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p496
  · intro a ha; simp [p496] at ha; subst a; trivial
  · exact checked496
theorem derived496 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c496 := by
  apply localUnsat_implies_entails f496 [c247, c248, c131] c496 unsat496 (by rfl) a
  have h0 : Entails.eval a c247 := h 246 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c497 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f497 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c151, some c343, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p497 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked497 : lratChecker f497 p497 = .success := by decide +kernel
theorem unsat497 : Unsatisfiable (PosFin 57) f497 := by
  apply lratCheckerSound f497 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p497
  · intro a ha; simp [p497] at ha; subst a; trivial
  · exact checked497
theorem derived497 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c497 := by
  apply localUnsat_implies_entails f497 [c153, c151, c343] c497 unsat497 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c498 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨43, by decide⟩, false), (⟨16, by decide⟩, true), (⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f498 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c190, some c497, some c313, some c354, some c163, some c364, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p498 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked498 : lratChecker f498 p498 = .success := by decide +kernel
theorem unsat498 : Unsatisfiable (PosFin 57) f498 := by
  apply lratCheckerSound f498 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p498
  · intro a ha; simp [p498] at ha; subst a; trivial
  · exact checked498
theorem derived498 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c498 := by
  apply localUnsat_implies_entails f498 [c184, c190, c497, c313, c354, c163, c364] c498 unsat498 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c497 := derived497 a h
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c163 := h 162 (by decide)
  have h6 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c499 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f499 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c494, some c489, some c382, some c378, some c338, some c341, some c491, some c495, some c496, some c227, some c219, some c250, some c120, some c385, some c498, some c160, some c170, some c320, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p499 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked499 : lratChecker f499 p499 = .success := by decide +kernel
theorem unsat499 : Unsatisfiable (PosFin 57) f499 := by
  apply lratCheckerSound f499 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p499
  · intro a ha; simp [p499] at ha; subst a; trivial
  · exact checked499
theorem derived499 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c499 := by
  apply localUnsat_implies_entails f499 [c494, c489, c382, c378, c338, c341, c491, c495, c496, c227, c219, c250, c120, c385, c498, c160, c170, c320] c499 unsat499 (by rfl) a
  have h0 : Entails.eval a c494 := derived494 a h
  have h1 : Entails.eval a c489 := derived489 a h
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c338 := h 337 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c491 := derived491 a h
  have h7 : Entails.eval a c495 := derived495 a h
  have h8 : Entails.eval a c496 := derived496 a h
  have h9 : Entails.eval a c227 := h 226 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c385 := derived385 a h
  have h14 : Entails.eval a c498 := derived498 a h
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c500 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f500 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c159, some c112, some c496, some c339, some c250, some c227, some c229, some c219, some c319, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p500 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked500 : lratChecker f500 p500 = .success := by decide +kernel
theorem unsat500 : Unsatisfiable (PosFin 57) f500 := by
  apply lratCheckerSound f500 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p500
  · intro a ha; simp [p500] at ha; subst a; trivial
  · exact checked500
theorem derived500 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c500 := by
  apply localUnsat_implies_entails f500 [c489, c159, c112, c496, c339, c250, c227, c229, c219, c319] c500 unsat500 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c496 := derived496 a h
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c250 := h 249 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  have h9 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c501 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f501 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c382, some c378, some c500, some c180, some c183, some c118, some c166, some c247, some c248, some c385, some c222, some c122, some c228, some c320, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p501 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked501 : lratChecker f501 p501 = .success := by decide +kernel
theorem unsat501 : Unsatisfiable (PosFin 57) f501 := by
  apply lratCheckerSound f501 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p501
  · intro a ha; simp [p501] at ha; subst a; trivial
  · exact checked501
theorem derived501 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c501 := by
  apply localUnsat_implies_entails f501 [c489, c382, c378, c500, c180, c183, c118, c166, c247, c248, c385, c222, c122, c228, c320] c501 unsat501 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c500 := derived500 a h
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c166 := h 165 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c385 := derived385 a h
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c502 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f502 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c494, some c499, some c501, some c181, some c185, some c194, some c118, some c247, some c248, some c222, some c343, some c352, some c152, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p502 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked502 : lratChecker f502 p502 = .success := by decide +kernel
theorem unsat502 : Unsatisfiable (PosFin 57) f502 := by
  apply lratCheckerSound f502 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p502
  · intro a ha; simp [p502] at ha; subst a; trivial
  · exact checked502
theorem derived502 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c502 := by
  apply localUnsat_implies_entails f502 [c489, c494, c499, c501, c181, c185, c194, c118, c247, c248, c222, c343, c352, c152] c502 unsat502 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c494 := derived494 a h
  have h2 : Entails.eval a c499 := derived499 a h
  have h3 : Entails.eval a c501 := derived501 a h
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c185 := h 184 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c247 := h 246 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c222 := h 221 (by decide)
  have h11 : Entails.eval a c343 := h 342 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c503 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f503 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c343, some c352, some c152, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p503 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked503 : lratChecker f503 p503 = .success := by decide +kernel
theorem unsat503 : Unsatisfiable (PosFin 57) f503 := by
  apply lratCheckerSound f503 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p503
  · intro a ha; simp [p503] at ha; subst a; trivial
  · exact checked503
theorem derived503 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c503 := by
  apply localUnsat_implies_entails f503 [c343, c352, c152] c503 unsat503 (by rfl) a
  have h0 : Entails.eval a c343 := h 342 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c504 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨28, by decide⟩, false), (⟨9, by decide⟩, true), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f504 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c470, some c133, some c267, some c298, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p504 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked504 : lratChecker f504 p504 = .success := by decide +kernel
theorem unsat504 : Unsatisfiable (PosFin 57) f504 := by
  apply lratCheckerSound f504 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p504
  · intro a ha; simp [p504] at ha; subst a; trivial
  · exact checked504
theorem derived504 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c504 := by
  apply localUnsat_implies_entails f504 [c470, c133, c267, c298] c504 unsat504 (by rfl) a
  have h0 : Entails.eval a c470 := derived470 a h
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c505 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨38, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f505 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c502, some c489, some c463, some c382, some c378, some c181, some c185, some c194, some c118, some c247, some c248, some c112, some c222, some c183, some c339, some c166, some c136, some c385, some c232, some c503, some c504, some c312, some c355, some c323, some c220, some c137, some c209, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p505 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked505 : lratChecker f505 p505 = .success := by decide +kernel
theorem unsat505 : Unsatisfiable (PosFin 57) f505 := by
  apply lratCheckerSound f505 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p505
  · intro a ha; simp [p505] at ha; subst a; trivial
  · exact checked505
theorem derived505 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c505 := by
  apply localUnsat_implies_entails f505 [c502, c489, c463, c382, c378, c181, c185, c194, c118, c247, c248, c112, c222, c183, c339, c166, c136, c385, c232, c503, c504, c312, c355, c323, c220, c137, c209] c505 unsat505 (by rfl) a
  have h0 : Entails.eval a c502 := derived502 a h
  have h1 : Entails.eval a c489 := derived489 a h
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c183 := h 182 (by decide)
  have h14 : Entails.eval a c339 := h 338 (by decide)
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c385 := derived385 a h
  have h18 : Entails.eval a c232 := h 231 (by decide)
  have h19 : Entails.eval a c503 := derived503 a h
  have h20 : Entails.eval a c504 := derived504 a h
  have h21 : Entails.eval a c312 := h 311 (by decide)
  have h22 : Entails.eval a c355 := h 354 (by decide)
  have h23 : Entails.eval a c323 := h 322 (by decide)
  have h24 : Entails.eval a c220 := h 219 (by decide)
  have h25 : Entails.eval a c137 := h 136 (by decide)
  have h26 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c506 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨33, by decide⟩, false), (⟨9, by decide⟩, true), (⟨40, by decide⟩, false), (⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f506 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c248, some c496, some c122, some c183, some c312, some c132, some c115, some c251, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p506 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked506 : lratChecker f506 p506 = .success := by decide +kernel
theorem unsat506 : Unsatisfiable (PosFin 57) f506 := by
  apply lratCheckerSound f506 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p506
  · intro a ha; simp [p506] at ha; subst a; trivial
  · exact checked506
theorem derived506 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c506 := by
  apply localUnsat_implies_entails f506 [c248, c496, c122, c183, c312, c132, c115, c251] c506 unsat506 (by rfl) a
  have h0 : Entails.eval a c248 := h 247 (by decide)
  have h1 : Entails.eval a c496 := derived496 a h
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c183 := h 182 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c507 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨48, by decide⟩, false), (⟨46, by decide⟩, true), (⟨14, by decide⟩, true), (⟨40, by decide⟩, false), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f507 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c157, some c167, some c323, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p507 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked507 : lratChecker f507 p507 = .success := by decide +kernel
theorem unsat507 : Unsatisfiable (PosFin 57) f507 := by
  apply lratCheckerSound f507 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p507
  · intro a ha; simp [p507] at ha; subst a; trivial
  · exact checked507
theorem derived507 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c507 := by
  apply localUnsat_implies_entails f507 [c157, c167, c323] c507 unsat507 (by rfl) a
  have h0 : Entails.eval a c157 := h 156 (by decide)
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c508 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨9, by decide⟩, true), (⟨40, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f508 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c339, some c463, some c382, some c378, some c506, some c118, some c22, some c180, some c112, some c250, some c229, some c219, some c385, some c311, some c169, some c115, some c507, some c355, some c252, some c14, some c407, some c323, some c23, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p508 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked508 : lratChecker f508 p508 = .success := by decide +kernel
theorem unsat508 : Unsatisfiable (PosFin 57) f508 := by
  apply lratCheckerSound f508 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p508
  · intro a ha; simp [p508] at ha; subst a; trivial
  · exact checked508
theorem derived508 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c508 := by
  apply localUnsat_implies_entails f508 [c489, c339, c463, c382, c378, c506, c118, c22, c180, c112, c250, c229, c219, c385, c311, c169, c115, c507, c355, c252, c14, c407, c323, c23] c508 unsat508 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c506 := derived506 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c229 := h 228 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c385 := derived385 a h
  have h14 : Entails.eval a c311 := h 310 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  have h16 : Entails.eval a c115 := h 114 (by decide)
  have h17 : Entails.eval a c507 := derived507 a h
  have h18 : Entails.eval a c355 := h 354 (by decide)
  have h19 : Entails.eval a c252 := h 251 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c407 := derived407 a h
  have h22 : Entails.eval a c323 := h 322 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c509 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨40, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f509 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c339, some c508, some c470, some c504, some c266, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p509 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked509 : lratChecker f509 p509 = .success := by decide +kernel
theorem unsat509 : Unsatisfiable (PosFin 57) f509 := by
  apply lratCheckerSound f509 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p509
  · intro a ha; simp [p509] at ha; subst a; trivial
  · exact checked509
theorem derived509 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c509 := by
  apply localUnsat_implies_entails f509 [c489, c339, c508, c470, c504, c266] c509 unsat509 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c470 := derived470 a h
  have h4 : Entails.eval a c504 := derived504 a h
  have h5 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c510 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f510 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c304, some c298, some c286, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p510 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked510 : lratChecker f510 p510 = .success := by decide +kernel
theorem unsat510 : Unsatisfiable (PosFin 57) f510 := by
  apply lratCheckerSound f510 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p510
  · intro a ha; simp [p510] at ha; subst a; trivial
  · exact checked510
theorem derived510 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c510 := by
  apply localUnsat_implies_entails f510 [c304, c298, c286] c510 unsat510 (by rfl) a
  have h0 : Entails.eval a c304 := h 303 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c511 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨35, by decide⟩, true), (⟨16, by decide⟩, true), (⟨38, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f511 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c267, some c138, some c3, some c45, some c296, some c297, some c150, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p511 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked511 : lratChecker f511 p511 = .success := by decide +kernel
theorem unsat511 : Unsatisfiable (PosFin 57) f511 := by
  apply lratCheckerSound f511 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p511
  · intro a ha; simp [p511] at ha; subst a; trivial
  · exact checked511
theorem derived511 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c511 := by
  apply localUnsat_implies_entails f511 [c42, c267, c138, c3, c45, c296, c297, c150] c511 unsat511 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c296 := h 295 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c512 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨35, by decide⟩, true), (⟨38, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f512 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c505, some c502, some c489, some c463, some c382, some c378, some c339, some c509, some c184, some c511, some c510, some c40, some c136, some c2, some c85, some c86, some c102, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p512 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked512 : lratChecker f512 p512 = .success := by decide +kernel
theorem unsat512 : Unsatisfiable (PosFin 57) f512 := by
  apply lratCheckerSound f512 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p512
  · intro a ha; simp [p512] at ha; subst a; trivial
  · exact checked512
theorem derived512 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c512 := by
  apply localUnsat_implies_entails f512 [c505, c502, c489, c463, c382, c378, c339, c509, c184, c511, c510, c40, c136, c2, c85, c86, c102] c512 unsat512 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c502 := derived502 a h
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c463 := derived463 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c339 := h 338 (by decide)
  have h7 : Entails.eval a c509 := derived509 a h
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c511 := derived511 a h
  have h10 : Entails.eval a c510 := derived510 a h
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c513 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨16, by decide⟩, true), (⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f513 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c159, some c248, some c180, some c118, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p513 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked513 : lratChecker f513 p513 = .success := by decide +kernel
theorem unsat513 : Unsatisfiable (PosFin 57) f513 := by
  apply lratCheckerSound f513 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p513
  · intro a ha; simp [p513] at ha; subst a; trivial
  · exact checked513
theorem derived513 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c513 := by
  apply localUnsat_implies_entails f513 [c114, c159, c248, c180, c118] c513 unsat513 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c514 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨52, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f514 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c136, some c247, some c209, some c220, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p514 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked514 : lratChecker f514 p514 = .success := by decide +kernel
theorem unsat514 : Unsatisfiable (PosFin 57) f514 := by
  apply lratCheckerSound f514 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p514
  · intro a ha; simp [p514] at ha; subst a; trivial
  · exact checked514
theorem derived514 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c514 := by
  apply localUnsat_implies_entails f514 [c118, c136, c247, c209, c220] c514 unsat514 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c247 := h 246 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c515 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f515 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c463, some c378, some c505, some c513, some c339, some c512, some c343, some c352, some c388, some c514, some c180, some c496, some c157, some c22, some c14, some c86, some c69, some c97, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p515 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked515 : lratChecker f515 p515 = .success := by decide +kernel
theorem unsat515 : Unsatisfiable (PosFin 57) f515 := by
  apply lratCheckerSound f515 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p515
  · intro a ha; simp [p515] at ha; subst a; trivial
  · exact checked515
theorem derived515 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c515 := by
  apply localUnsat_implies_entails f515 [c489, c463, c378, c505, c513, c339, c512, c343, c352, c388, c514, c180, c496, c157, c22, c14, c86, c69, c97] c515 unsat515 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c463 := derived463 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c505 := derived505 a h
  have h4 : Entails.eval a c513 := derived513 a h
  have h5 : Entails.eval a c339 := h 338 (by decide)
  have h6 : Entails.eval a c512 := derived512 a h
  have h7 : Entails.eval a c343 := h 342 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c388 := derived388 a h
  have h10 : Entails.eval a c514 := derived514 a h
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c496 := derived496 a h
  have h13 : Entails.eval a c157 := h 156 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c86 := h 85 (by decide)
  have h17 : Entails.eval a c69 := h 68 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c516 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f516 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c463, some c378, some c502, some c515, some c338, some c341, some c491, some c495, some c496, some c118, some c22, some c219, some c250, some c251, some c257, some c131, some c261, some c129, some c189, some c14, some c123, some c86, some c2, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p516 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked516 : lratChecker f516 p516 = .success := by decide +kernel
theorem unsat516 : Unsatisfiable (PosFin 57) f516 := by
  apply lratCheckerSound f516 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p516
  · intro a ha; simp [p516] at ha; subst a; trivial
  · exact checked516
theorem derived516 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c516 := by
  apply localUnsat_implies_entails f516 [c489, c463, c378, c502, c515, c338, c341, c491, c495, c496, c118, c22, c219, c250, c251, c257, c131, c261, c129, c189, c14, c123, c86, c2] c516 unsat516 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c463 := derived463 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c502 := derived502 a h
  have h4 : Entails.eval a c515 := derived515 a h
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c341 := h 340 (by decide)
  have h7 : Entails.eval a c491 := derived491 a h
  have h8 : Entails.eval a c495 := derived495 a h
  have h9 : Entails.eval a c496 := derived496 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c131 := h 130 (by decide)
  have h17 : Entails.eval a c261 := h 260 (by decide)
  have h18 : Entails.eval a c129 := h 128 (by decide)
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c123 := h 122 (by decide)
  have h22 : Entails.eval a c86 := h 85 (by decide)
  have h23 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c517 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨38, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f517 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c489, some c491, some c341, some c338, some c516, some c463, some c378, some c181, some c496, some c22, some c219, some c250, some c127, some c131, some c251, some c257, some c261, some c129, some c191, some c14, some c123, some c86, some c2, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p517 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked517 : lratChecker f517 p517 = .success := by decide +kernel
theorem unsat517 : Unsatisfiable (PosFin 57) f517 := by
  apply lratCheckerSound f517 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p517
  · intro a ha; simp [p517] at ha; subst a; trivial
  · exact checked517
theorem derived517 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c517 := by
  apply localUnsat_implies_entails f517 [c489, c491, c341, c338, c516, c463, c378, c181, c496, c22, c219, c250, c127, c131, c251, c257, c261, c129, c191, c14, c123, c86, c2] c517 unsat517 (by rfl) a
  have h0 : Entails.eval a c489 := derived489 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c341 := h 340 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c463 := derived463 a h
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c496 := derived496 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c131 := h 130 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c129 := h 128 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c86 := h 85 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c518 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f518 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c466, some c354, some c355, some c368, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p518 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked518 : lratChecker f518 p518 = .success := by decide +kernel
theorem unsat518 : Unsatisfiable (PosFin 57) f518 := by
  apply lratCheckerSound f518 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p518
  · intro a ha; simp [p518] at ha; subst a; trivial
  · exact checked518
theorem derived518 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c518 := by
  apply localUnsat_implies_entails f518 [c466, c354, c355, c368] c518 unsat518 (by rfl) a
  have h0 : Entails.eval a c466 := derived466 a h
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c519 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c516, some c489, some c463, some c382, some c378, some c338, some c491, some c517, some c164, some c136, some c510, some c145, some c518, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 57) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c516, c489, c463, c382, c378, c338, c491, c517, c164, c136, c510, c145, c518] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c516 := derived516 a h
  have h1 : Entails.eval a c489 := derived489 a h
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c491 := derived491 a h
  have h7 : Entails.eval a c517 := derived517 a h
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c510 := derived510 a h
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c518 := derived518 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c519, some c516, some c489, some c382, some c378, some c164, some c180, some c181, some c112, some c165, some c496, some c250, some c385, some c229, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 57) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c519, c516, c489, c382, c378, c164, c180, c181, c112, c165, c496, c250, c385, c229] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c519 := derived519 a h
  have h1 : Entails.eval a c516 := derived516 a h
  have h2 : Entails.eval a c489 := derived489 a h
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c164 := h 163 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c181 := h 180 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c496 := derived496 a h
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c385 := derived385 a h
  have h13 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c516, some c382, some c463, some c378, some c520, some c518, some c135, some c519, some c489, some c180, some c181, some c159, some c112, some c496, some c320, some c250, some c169, some c229, some c385, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 57) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c516, c382, c463, c378, c520, c518, c135, c519, c489, c180, c181, c159, c112, c496, c320, c250, c169, c229, c385] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c516 := derived516 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c520 := derived520 a h
  have h5 : Entails.eval a c518 := derived518 a h
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c519 := derived519 a h
  have h8 : Entails.eval a c489 := derived489 a h
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c181 := h 180 (by decide)
  have h11 : Entails.eval a c159 := h 158 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c496 := derived496 a h
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c385 := derived385 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c463, some c382, some c378, some c489, some c516, some c519, some c520, some c518, some c135, some c521, some c118, some c247, some c248, some c222, some c339, some c343, some c352, some c388, some c514, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 57) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c463, c382, c378, c489, c516, c519, c520, c518, c135, c521, c118, c247, c248, c222, c339, c343, c352, c388, c514] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c463 := derived463 a h
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c489 := derived489 a h
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c519 := derived519 a h
  have h6 : Entails.eval a c520 := derived520 a h
  have h7 : Entails.eval a c518 := derived518 a h
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c521 := derived521 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c247 := h 246 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c339 := h 338 (by decide)
  have h15 : Entails.eval a c343 := h 342 (by decide)
  have h16 : Entails.eval a c352 := h 351 (by decide)
  have h17 : Entails.eval a c388 := derived388 a h
  have h18 : Entails.eval a c514 := derived514 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨11, by decide⟩, false), (⟨40, by decide⟩, true), (⟨27, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c44, some c179, some c13, some c47, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 57) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c140, c44, c179, c13, c47] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨15, by decide⟩, true), (⟨24, by decide⟩, false), (⟨20, by decide⟩, true), (⟨12, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c355, some c366, some c365, some c363, some c402, some c170, some c168, some c261, some c194, some c126, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 57) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c378, c355, c366, c365, c363, c402, c170, c168, c261, c194, c126] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c365 := h 364 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c402 := derived402 a h
  have h6 : Entails.eval a c170 := h 169 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c365, some c354, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 57) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c371, c365, c354] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c365 := h 364 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c373, some c355, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 57) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c364, c373, c355] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c355, some c370, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c354, c355, c370] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c464, some c56, some c74, some c83, some c86, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c464, c56, c74, c83, c86] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c464 := derived464 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨15, by decide⟩, true), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c526, some c382, some c525, some c527, some c363, some c121, some c250, some c232, some c170, some c168, some c230, some c195, some c262, some c524, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c378, c526, c382, c525, c527, c363, c121, c250, c232, c170, c168, c230, c195, c262, c524] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c526 := derived526 a h
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c525 := derived525 a h
  have h4 : Entails.eval a c527 := derived527 a h
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c230 := h 229 (by decide)
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c524 := derived524 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨27, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c528, some c284, some c274, some c287, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c528, c284, c274, c287] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c528 := derived528 a h
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c382, some c527, some c525, some c518, some c526, some c530, some c529, some c183, some c169, some c167, some c195, some c194, some c144, some c145, some c510, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c378, c382, c527, c525, c518, c526, c530, c529, c183, c169, c167, c195, c194, c144, c145, c510] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c527 := derived527 a h
  have h3 : Entails.eval a c525 := derived525 a h
  have h4 : Entails.eval a c518 := derived518 a h
  have h5 : Entails.eval a c526 := derived526 a h
  have h6 : Entails.eval a c530 := derived530 a h
  have h7 : Entails.eval a c529 := derived529 a h
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c169 := h 168 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c510 := derived510 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c527, some c274, some c286, some c287, some c303, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c527, c274, c286, c287, c303] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c527 := derived527 a h
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨28, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c286, some c74, some c48, some c40, some c56, some c338, some c339, some c309, some c95, some c96, some c133, some c58, some c71, some c1, some c305, some c3, some c145, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c45, c286, c74, c48, c40, c56, c338, c339, c309, c95, c96, c133, c58, c71, c1, c305, c3, c145] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c338 := h 337 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c165, some c169, some c167, some c194, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c165, c169, c167, c194] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c165 := h 164 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨27, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨45, by decide⟩, true), (⟨28, by decide⟩, true), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c179, some c194, some c289, some c168, some c180, some c276, some c146, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c179, c194, c289, c168, c180, c276, c146] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c179 := h 178 (by decide)
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c289 := h 288 (by decide)
  have h3 : Entails.eval a c168 := h 167 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨48, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c170, some c276, some c150, some c146, some c139, some c200, some c186, some c311, some c107, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c122, c170, c276, c150, c146, c139, c200, c186, c311, c107] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨45, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c382, some c522, some c525, some c463, some c531, some c527, some c366, some c534, some c183, some c532, some c533, some c536, some c535, some c135, some c144, some c117, some c180, some c469, some c289, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c378, c382, c522, c525, c463, c531, c527, c366, c534, c183, c532, c533, c536, c535, c135, c144, c117, c180, c469, c289] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c525 := derived525 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c531 := derived531 a h
  have h6 : Entails.eval a c527 := derived527 a h
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c534 := derived534 a h
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c532 := derived532 a h
  have h11 : Entails.eval a c533 := derived533 a h
  have h12 : Entails.eval a c536 := derived536 a h
  have h13 : Entails.eval a c535 := derived535 a h
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c469 := derived469 a h
  have h19 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c302, some c296, some c286, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c302, c296, c286] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c302 := h 301 (by decide)
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c527, some c74, some c85, some c86, some c102, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c527, c74, c85, c86, c102] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c527 := derived527 a h
  have h1 : Entails.eval a c74 := h 73 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, true), (⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c85, some c86, some c19, some c100, some c56, some c297, some c196, some c271, some c228, some c198, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c45, c85, c86, c19, c100, c56, c297, c196, c271, c228, c198] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  have h10 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨41, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c40, some c338, some c382, some c378, some c56, some c538, some c58, some c76, some c99, some c24, some c250, some c247, some c121, some c30, some c4, some c470, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c48, c40, c338, c382, c378, c56, c538, c58, c76, c99, c24, c250, c247, c121, c30, c4, c470] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c338 := h 337 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c538 := derived538 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c250 := h 249 (by decide)
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c470 := derived470 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨39, by decide⟩, false), (⟨31, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c65, some c305, some c302, some c348, some c267, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c46, c65, c305, c302, c348, c267] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c382, some c463, some c522, some c525, some c527, some c531, some c532, some c539, some c48, some c40, some c338, some c339, some c309, some c540, some c541, some c95, some c96, some c58, some c72, some c44, some c26, some c248, some c542, some c538, some c32, some c100, some c537, some c250, some c49, some c321, some c212, some c220, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c378, c382, c463, c522, c525, c527, c531, c532, c539, c48, c40, c338, c339, c309, c540, c541, c95, c96, c58, c72, c44, c26, c248, c542, c538, c32, c100, c537, c250, c49, c321, c212, c220] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c382 := h 381 (by decide)
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c525 := derived525 a h
  have h5 : Entails.eval a c527 := derived527 a h
  have h6 : Entails.eval a c531 := derived531 a h
  have h7 : Entails.eval a c532 := derived532 a h
  have h8 : Entails.eval a c539 := derived539 a h
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c339 := h 338 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c540 := derived540 a h
  have h15 : Entails.eval a c541 := derived541 a h
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c96 := h 95 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c72 := h 71 (by decide)
  have h20 : Entails.eval a c44 := h 43 (by decide)
  have h21 : Entails.eval a c26 := h 25 (by decide)
  have h22 : Entails.eval a c248 := h 247 (by decide)
  have h23 : Entails.eval a c542 := derived542 a h
  have h24 : Entails.eval a c538 := derived538 a h
  have h25 : Entails.eval a c32 := h 31 (by decide)
  have h26 : Entails.eval a c100 := h 99 (by decide)
  have h27 : Entails.eval a c537 := derived537 a h
  have h28 : Entails.eval a c250 := h 249 (by decide)
  have h29 : Entails.eval a c49 := h 48 (by decide)
  have h30 : Entails.eval a c321 := h 320 (by decide)
  have h31 : Entails.eval a c212 := h 211 (by decide)
  have h32 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨36, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c73, some c360, some c358, some c321, some c246, some c227, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c75, c73, c360, c358, c321, c246, c227] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c339, some c384, some c377, some c49, some c91, some c99, some c58, some c538, some c56, some c96, some c44, some c26, some c212, some c248, some c23, some c349, some c65, some c544, some c354, some c527, some c80, some c77, some c227, some c358, some c246, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c40, c339, c384, c377, c49, c91, c99, c58, c538, c56, c96, c44, c26, c212, c248, c23, c349, c65, c544, c354, c527, c80, c77, c227, c358, c246] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c384 := h 383 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c538 := derived538 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c212 := h 211 (by decide)
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c544 := derived544 a h
  have h19 : Entails.eval a c354 := h 353 (by decide)
  have h20 : Entails.eval a c527 := derived527 a h
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c77 := h 76 (by decide)
  have h23 : Entails.eval a c227 := h 226 (by decide)
  have h24 : Entails.eval a c358 := h 357 (by decide)
  have h25 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨40, by decide⟩, true), (⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c95, some c96, some c100, some c58, some c72, some c65, some c542, some c350, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c40, c95, c96, c100, c58, c72, c65, c542, c350] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c542 := derived542 a h
  have h8 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c297, some c306, some c287, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c297, c306, c287] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c297 := h 296 (by decide)
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c339, some c384, some c377, some c545, some c546, some c56, some c518, some c538, some c58, some c99, some c89, some c547, some c140, some c44, some c179, some c181, some c5, some c117, some c164, some c470, some c527, some c309, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c40, c339, c384, c377, c545, c546, c56, c518, c538, c58, c99, c89, c547, c140, c44, c179, c181, c5, c117, c164, c470, c527, c309] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c384 := h 383 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c545 := derived545 a h
  have h5 : Entails.eval a c546 := derived546 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c518 := derived518 a h
  have h8 : Entails.eval a c538 := derived538 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c547 := derived547 a h
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c181 := h 180 (by decide)
  have h17 : Entails.eval a c5 := h 4 (by decide)
  have h18 : Entails.eval a c117 := h 116 (by decide)
  have h19 : Entails.eval a c164 := h 163 (by decide)
  have h20 : Entails.eval a c470 := derived470 a h
  have h21 : Entails.eval a c527 := derived527 a h
  have h22 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c384, some c377, some c40, some c339, some c548, some c45, some c85, some c86, some c100, some c56, some c518, some c538, some c547, some c58, some c140, some c104, some c181, some c89, some c179, some c117, some c164, some c196, some c527, some c309, some c19, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c384, c377, c40, c339, c548, c45, c85, c86, c100, c56, c518, c538, c547, c58, c140, c104, c181, c89, c179, c117, c164, c196, c527, c309, c19] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c384 := h 383 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c548 := derived548 a h
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c518 := derived518 a h
  have h11 : Entails.eval a c538 := derived538 a h
  have h12 : Entails.eval a c547 := derived547 a h
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c104 := h 103 (by decide)
  have h16 : Entails.eval a c181 := h 180 (by decide)
  have h17 : Entails.eval a c89 := h 88 (by decide)
  have h18 : Entails.eval a c179 := h 178 (by decide)
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c164 := h 163 (by decide)
  have h21 : Entails.eval a c196 := h 195 (by decide)
  have h22 : Entails.eval a c527 := derived527 a h
  have h23 : Entails.eval a c309 := h 308 (by decide)
  have h24 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c98, some c86, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c106, c98, c86] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c86, some c102, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c85, c86, c102] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c89, some c336, some c178, some c109, some c67, some c470, some c346, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c543, c89, c336, c178, c109, c67, c470, c346] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c470 := derived470 a h
  have h7 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨52, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c549, some c377, some c384, some c551, some c97, some c550, some c538, some c547, some c44, some c62, some c339, some c136, some c268, some c181, some c150, some c2, some c552, some c95, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c543, c549, c377, c384, c551, c97, c550, c538, c547, c44, c62, c339, c136, c268, c181, c150, c2, c552, c95] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c549 := derived549 a h
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c551 := derived551 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c550 := derived550 a h
  have h7 : Entails.eval a c538 := derived538 a h
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c181 := h 180 (by decide)
  have h15 : Entails.eval a c150 := h 149 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c552 := derived552 a h
  have h18 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨27, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, false), (⟨28, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c339, some c136, some c266, some c2, some c14, some c503, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c339, c136, c266, c2, c14, c503] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c339 := h 338 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c503 := derived503 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c377, some c384, some c549, some c550, some c551, some c97, some c50, some c91, some c102, some c46, some c553, some c305, some c554, some c71, some c65, some c350, some c351, some c268, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c543, c377, c384, c549, c550, c551, c97, c50, c91, c102, c46, c553, c305, c554, c71, c65, c350, c351, c268] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c384 := h 383 (by decide)
  have h3 : Entails.eval a c549 := derived549 a h
  have h4 : Entails.eval a c550 := derived550 a h
  have h5 : Entails.eval a c551 := derived551 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c553 := derived553 a h
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c554 := derived554 a h
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c350 := h 349 (by decide)
  have h17 : Entails.eval a c351 := h 350 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨30, by decide⟩, false), (⟨8, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c65, some c305, some c350, some c351, some c268, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c46, c65, c305, c350, c351, c268] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c97, some c50, some c98, some c44, some c26, some c71, some c556, some c102, some c91, some c383, some c249, some c289, some c89, some c33, some c306, some c95, some c60, some c34, some c213, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c48, c97, c50, c98, c44, c26, c71, c556, c102, c91, c383, c249, c289, c89, c33, c306, c95, c60, c34, c213] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c306 := h 305 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c34 := h 33 (by decide)
  have h19 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨52, by decide⟩, true), (⟨28, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c97, some c50, some c98, some c91, some c383, some c340, some c289, some c89, some c23, some c41, some c95, some c249, some c306, some c36, some c35, some c62, some c213, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c48, c97, c50, c98, c91, c383, c340, c289, c89, c23, c41, c95, c249, c306, c36, c35, c62, c213] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c340 := h 339 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c97, some c383, some c340, some c89, some c137, some c95, some c14, some c62, some c136, some c297, some c345, some c264, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c98, c97, c383, c340, c89, c137, c95, c14, c62, c136, c297, c345, c264] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c340 := h 339 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c137 := h 136 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c345 := h 344 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c297, some c547, some c328, some c133, some c264, some c2, some c353, some c136, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c297, c547, c328, c133, c264, c2, c353, c136] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c297 := h 296 (by decide)
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨5, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c50, some c305, some c102, some c98, some c301, some c559, some c560, some c62, some c95, some c89, some c336, some c21, some c246, some c201, some c29, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c97, c50, c305, c102, c98, c301, c559, c560, c62, c95, c89, c336, c21, c246, c201, c29] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c559 := derived559 a h
  have h7 : Entails.eval a c560 := derived560 a h
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c246 := h 245 (by decide)
  have h14 : Entails.eval a c201 := h 200 (by decide)
  have h15 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨52, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c557, some c558, some c102, some c46, some c561, some c289, some c336, some c135, some c39, some c266, some c11, some c1, some c345, some c353, some c152, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c48, c557, c558, c102, c46, c561, c289, c336, c135, c39, c266, c11, c1, c345, c353, c152] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c557 := derived557 a h
  have h2 : Entails.eval a c558 := derived558 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c561 := derived561 a h
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c266 := h 265 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c345 := h 344 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c12, some c148, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c11, c12, c148] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨31, by decide⟩, true), (⟨29, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c348, some c352, some c270, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c348, c352, c270] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c348 := h 347 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨40, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c555, some c562, some c48, some c106, some c102, some c46, some c85, some c374, some c328, some c289, some c19, some c37, some c63, some c301, some c302, some c238, some c237, some c196, some c36, some c564, some c21, some c109, some c563, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c543, c555, c562, c48, c106, c102, c46, c85, c374, c328, c289, c19, c37, c63, c301, c302, c238, c237, c196, c36, c564, c21, c109, c563] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c555 := derived555 a h
  have h2 : Entails.eval a c562 := derived562 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c374 := h 373 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c301 := h 300 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c238 := h 237 (by decide)
  have h17 : Entails.eval a c237 := h 236 (by decide)
  have h18 : Entails.eval a c196 := h 195 (by decide)
  have h19 : Entails.eval a c36 := h 35 (by decide)
  have h20 : Entails.eval a c564 := derived564 a h
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c109 := h 108 (by decide)
  have h23 : Entails.eval a c563 := derived563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c41, some c340, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c49, c41, c340] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c91, some c383, some c340, some c89, some c69, some c64, some c101, some c346, some c70, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c103, c91, c383, c340, c89, c69, c64, c101, c346, c70] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c340 := h 339 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c555, some c562, some c48, some c565, some c566, some c567, some c46, some c85, some c301, some c374, some c289, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c543, c555, c562, c48, c565, c566, c567, c46, c85, c301, c374, c289] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c555 := derived555 a h
  have h2 : Entails.eval a c562 := derived562 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c565 := derived565 a h
  have h5 : Entails.eval a c566 := derived566 a h
  have h6 : Entails.eval a c567 := derived567 a h
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨1, by decide⟩, true), (⟨52, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c85, some c374, some c289, some c301, some c302, some c41, some c54, some c297, some c44, some c140, some c272, some c16, some c327, some c136, some c63, some c349, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c48, c85, c374, c289, c301, c302, c41, c54, c297, c44, c140, c272, c16, c327, c136, c63, c349] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c327 := h 326 (by decide)
  have h14 : Entails.eval a c136 := h 135 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c568, some c543, some c555, some c562, some c48, some c569, some c103, some c50, some c91, some c305, some c383, some c289, some c89, some c301, some c101, some c60, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c568, c543, c555, c562, c48, c569, c103, c50, c91, c305, c383, c289, c89, c301, c101, c60] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c568 := derived568 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c555 := derived555 a h
  have h3 : Entails.eval a c562 := derived562 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c569 := derived569 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c301 := h 300 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c568, some c543, some c555, some c562, some c48, some c570, some c106, some c102, some c26, some c65, some c85, some c238, some c374, some c19, some c289, some c327, some c301, some c302, some c268, some c270, some c349, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c568, c543, c555, c562, c48, c570, c106, c102, c26, c65, c85, c238, c374, c19, c289, c327, c301, c302, c268, c270, c349] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c568 := derived568 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c555 := derived555 a h
  have h3 : Entails.eval a c562 := derived562 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c570 := derived570 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c238 := h 237 (by decide)
  have h12 : Entails.eval a c374 := h 373 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c327 := h 326 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c302 := h 301 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c60, some c300, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c54, c60, c300] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c555, some c48, some c562, some c568, some c571, some c46, some c103, some c102, some c50, some c91, some c383, some c289, some c89, some c101, some c572, some c306, some c44, some c140, some c265, some c16, some c136, some c349, some c350, some c69, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c543, c555, c48, c562, c568, c571, c46, c103, c102, c50, c91, c383, c289, c89, c101, c572, c306, c44, c140, c265, c16, c136, c349, c350, c69] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c555 := derived555 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c562 := derived562 a h
  have h4 : Entails.eval a c568 := derived568 a h
  have h5 : Entails.eval a c571 := derived571 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c383 := h 382 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c572 := derived572 a h
  have h16 : Entails.eval a c306 := h 305 (by decide)
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c140 := h 139 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c136 := h 135 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  have h23 : Entails.eval a c350 := h 349 (by decide)
  have h24 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c543, some c103, some c567, some c50, some c91, some c510, some c304, some c298, some c383, some c54, some c37, some c89, some c307, some c327, some c101, some c44, some c140, some c265, some c70, some c16, some c13, some c349, some c347, some c154, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c573, c543, c103, c567, c50, c91, c510, c304, c298, c383, c54, c37, c89, c307, c327, c101, c44, c140, c265, c70, c16, c13, c349, c347, c154] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c567 := derived567 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c510 := derived510 a h
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c307 := h 306 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c101 := h 100 (by decide)
  have h16 : Entails.eval a c44 := h 43 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c70 := h 69 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c13 := h 12 (by decide)
  have h22 : Entails.eval a c349 := h 348 (by decide)
  have h23 : Entails.eval a c347 := h 346 (by decide)
  have h24 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c303, some c307, some c510, some c298, some c37, some c328, some c327, some c265, some c68, some c70, some c349, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c573, c303, c307, c510, c298, c37, c328, c327, c265, c68, c70, c349] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c510 := derived510 a h
  have h4 : Entails.eval a c298 := h 297 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c327 := h 326 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c70 := h 69 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c271, some c351, some c350, some c68, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c265, c271, c351, c350, c68] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨40, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c34, some c28, some c340, some c237, some c86, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c23, c34, c28, c340, c237, c86] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c340 := h 339 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c303, some c307, some c575, some c576, some c577, some c209, some c22, some c345, some c353, some c64, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c573, c303, c307, c575, c576, c577, c209, c22, c345, c353, c64] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c576 := derived576 a h
  have h5 : Entails.eval a c577 := derived577 a h
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c104, some c88, some c91, some c383, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c101, c104, c88, c91, c383] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c578, some c49, some c54, some c60, some c572, some c383, some c296, some c290, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c543, c578, c49, c54, c60, c572, c383, c296, c290] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c578 := derived578 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c572 := derived572 a h
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c574, some c580, some c104, some c579, some c91, some c384, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c543, c574, c580, c104, c579, c91, c384] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c574 := derived574 a h
  have h2 : Entails.eval a c580 := derived580 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c543, some c581, some c46, some c85, some c303, some c304, some c374, some c49, some c54, some c566, some c50, some c290, some c299, some c140, some c302, some c182, some c60, some c148, some c147, some c18, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c573, c543, c581, c46, c85, c303, c304, c374, c49, c54, c566, c50, c290, c299, c140, c302, c182, c60, c148, c147, c18] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c303 := h 302 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c566 := derived566 a h
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c303, some c304, some c49, some c50, some c383, some c99, some c290, some c60, some c302, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c303, c304, c49, c50, c383, c99, c290, c60, c302] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c303 := h 302 (by decide)
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c573, some c582, some c583, some c41, some c566, some c44, some c26, some c72, some c211, some c299, some c22, some c286, some c349, some c327, some c263, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c543, c573, c582, c583, c41, c566, c44, c26, c72, c211, c299, c22, c286, c349, c327, c263] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c573 := derived573 a h
  have h2 : Entails.eval a c582 := derived582 a h
  have h3 : Entails.eval a c583 := derived583 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c566 := derived566 a h
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c349 := h 348 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived584

end CochromaticTwenty.Certificates.B16_4_1
