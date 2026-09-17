import MerLeanExperiment.Certificates.B16_8_0Enumerating.Steps0000_0099

/-! Generated from the actual pinned b16_8_0-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_0Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c519 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f519 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c385, some c453, some c89, some c514, some c102, some c515, some c67, some c506, some c464, some c518, some c66, some c517, some c46, some c300, some c297, some c467, some c190, some c344, some c240, some c507, some c197, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p519 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked519 : lratChecker f519 p519 = .success := by decide +kernel
theorem unsat519 : Unsatisfiable (PosFin 57) f519 := by
  apply lratCheckerSound f519 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p519
  · intro a ha; simp [p519] at ha; subst a; trivial
  · exact checked519
theorem derived519 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c519 := by
  apply localUnsat_implies_entails f519 [c381, c385, c453, c89, c514, c102, c515, c67, c506, c464, c518, c66, c517, c46, c300, c297, c467, c190, c344, c240, c507, c197] c519 unsat519 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c514 := derived514 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c515 := derived515 a h
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c506 := derived506 a h
  have h9 : Entails.eval a c464 := derived464 a h
  have h10 : Entails.eval a c518 := derived518 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c517 := derived517 a h
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c300 := h 299 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c467 := derived467 a h
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c344 := h 343 (by decide)
  have h19 : Entails.eval a c240 := h 239 (by decide)
  have h20 : Entails.eval a c507 := derived507 a h
  have h21 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c520 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨31, by decide⟩, true), (⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f520 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c517, some c267, some c507, some c193, some c301, some c197, some c246, some c242, some c214, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p520 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked520 : lratChecker f520 p520 = .success := by decide +kernel
theorem unsat520 : Unsatisfiable (PosFin 57) f520 := by
  apply lratCheckerSound f520 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p520
  · intro a ha; simp [p520] at ha; subst a; trivial
  · exact checked520
theorem derived520 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c520 := by
  apply localUnsat_implies_entails f520 [c506, c517, c267, c507, c193, c301, c197, c246, c242, c214] c520 unsat520 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c517 := derived517 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c507 := derived507 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  have h8 : Entails.eval a c242 := h 241 (by decide)
  have h9 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c521 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨26, by decide⟩, true), (⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f521 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c249, some c214, some c198, some c240, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p521 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked521 : lratChecker f521 p521 = .success := by decide +kernel
theorem unsat521 : Unsatisfiable (PosFin 57) f521 := by
  apply lratCheckerSound f521 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p521
  · intro a ha; simp [p521] at ha; subst a; trivial
  · exact checked521
theorem derived521 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c521 := by
  apply localUnsat_implies_entails f521 [c34, c249, c214, c198, c240] c521 unsat521 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c249 := h 248 (by decide)
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c522 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f522 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c453, some c89, some c519, some c104, some c381, some c514, some c102, some c515, some c506, some c38, some c517, some c297, some c520, some c344, some c61, some c521, some c213, some c246, some c240, some c198, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p522 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked522 : lratChecker f522 p522 = .success := by decide +kernel
theorem unsat522 : Unsatisfiable (PosFin 57) f522 := by
  apply lratCheckerSound f522 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p522
  · intro a ha; simp [p522] at ha; subst a; trivial
  · exact checked522
theorem derived522 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c522 := by
  apply localUnsat_implies_entails f522 [c385, c453, c89, c519, c104, c381, c514, c102, c515, c506, c38, c517, c297, c520, c344, c61, c521, c213, c246, c240, c198] c522 unsat522 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c519 := derived519 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c514 := derived514 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c515 := derived515 a h
  have h9 : Entails.eval a c506 := derived506 a h
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c517 := derived517 a h
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c520 := derived520 a h
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c521 := derived521 a h
  have h17 : Entails.eval a c213 := h 212 (by decide)
  have h18 : Entails.eval a c246 := h 245 (by decide)
  have h19 : Entails.eval a c240 := h 239 (by decide)
  have h20 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c523 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f523 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c385, some c453, some c89, some c514, some c102, some c515, some c506, some c522, some c341, some c335, some c507, some c36, some c293, some c291, some c194, some c267, some c242, some c300, some c209, some c202, some c246, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p523 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked523 : lratChecker f523 p523 = .success := by decide +kernel
theorem unsat523 : Unsatisfiable (PosFin 57) f523 := by
  apply lratCheckerSound f523 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p523
  · intro a ha; simp [p523] at ha; subst a; trivial
  · exact checked523
theorem derived523 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c523 := by
  apply localUnsat_implies_entails f523 [c381, c385, c453, c89, c514, c102, c515, c506, c522, c341, c335, c507, c36, c293, c291, c194, c267, c242, c300, c209, c202, c246] c523 unsat523 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c514 := derived514 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c515 := derived515 a h
  have h7 : Entails.eval a c506 := derived506 a h
  have h8 : Entails.eval a c522 := derived522 a h
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c335 := h 334 (by decide)
  have h11 : Entails.eval a c507 := derived507 a h
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c293 := h 292 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c242 := h 241 (by decide)
  have h18 : Entails.eval a c300 := h 299 (by decide)
  have h19 : Entails.eval a c209 := h 208 (by decide)
  have h20 : Entails.eval a c202 := h 201 (by decide)
  have h21 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c524 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f524 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c297, some c50, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p524 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked524 : lratChecker f524 p524 = .success := by decide +kernel
theorem unsat524 : Unsatisfiable (PosFin 57) f524 := by
  apply lratCheckerSound f524 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p524
  · intro a ha; simp [p524] at ha; subst a; trivial
  · exact checked524
theorem derived524 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c524 := by
  apply localUnsat_implies_entails f524 [c300, c297, c50] c524 unsat524 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c297 := h 296 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c525 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f525 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c385, some c453, some c89, some c514, some c102, some c515, some c519, some c104, some c67, some c523, some c66, some c367, some c65, some c99, some c524, some c506, some c507, some c267, some c193, some c301, some c31, some c45, some c204, some c309, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p525 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked525 : lratChecker f525 p525 = .success := by decide +kernel
theorem unsat525 : Unsatisfiable (PosFin 57) f525 := by
  apply lratCheckerSound f525 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p525
  · intro a ha; simp [p525] at ha; subst a; trivial
  · exact checked525
theorem derived525 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c525 := by
  apply localUnsat_implies_entails f525 [c381, c385, c453, c89, c514, c102, c515, c519, c104, c67, c523, c66, c367, c65, c99, c524, c506, c507, c267, c193, c301, c31, c45, c204, c309] c525 unsat525 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c514 := derived514 a h
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c515 := derived515 a h
  have h7 : Entails.eval a c519 := derived519 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c523 := derived523 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c524 := derived524 a h
  have h16 : Entails.eval a c506 := derived506 a h
  have h17 : Entails.eval a c507 := derived507 a h
  have h18 : Entails.eval a c267 := h 266 (by decide)
  have h19 : Entails.eval a c193 := h 192 (by decide)
  have h20 : Entails.eval a c301 := h 300 (by decide)
  have h21 : Entails.eval a c31 := h 30 (by decide)
  have h22 : Entails.eval a c45 := h 44 (by decide)
  have h23 : Entails.eval a c204 := h 203 (by decide)
  have h24 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c526 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f526 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c453, some c385, some c381, some c67, some c89, some c514, some c102, some c515, some c519, some c104, some c523, some c66, some c367, some c65, some c99, some c525, some c344, some c341, some c61, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p526 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked526 : lratChecker f526 p526 = .success := by decide +kernel
theorem unsat526 : Unsatisfiable (PosFin 57) f526 := by
  apply lratCheckerSound f526 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p526
  · intro a ha; simp [p526] at ha; subst a; trivial
  · exact checked526
theorem derived526 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c526 := by
  apply localUnsat_implies_entails f526 [c453, c385, c381, c67, c89, c514, c102, c515, c519, c104, c523, c66, c367, c65, c99, c525, c344, c341, c61] c526 unsat526 (by rfl) a
  have h0 : Entails.eval a c453 := derived453 a h
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c514 := derived514 a h
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c519 := derived519 a h
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c523 := derived523 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c525 := derived525 a h
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c527 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨31, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c507, some c267, some c193, some c301, some c31, some c45, some c204, some c309, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c506, c507, c267, c193, c301, c31, c45, c204, c309] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c507 := derived507 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c524, some c527, some c344, some c341, some c61, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c104, c524, c527, c344, c341, c61] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c524 := derived524 a h
  have h2 : Entails.eval a c527 := derived527 a h
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c341, some c61, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c344, c341, c61] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c453, some c381, some c528, some c84, some c98, some c524, some c529, some c267, some c301, some c52, some c45, some c309, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c506, c453, c381, c528, c84, c98, c524, c529, c267, c301, c52, c45, c309] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c528 := derived528 a h
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c524 := derived524 a h
  have h7 : Entails.eval a c529 := derived529 a h
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c69, some c52, some c275, some c281, some c76, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c45, c69, c52, c275, c281, c76] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c281 := h 280 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c530, some c526, some c506, some c453, some c385, some c64, some c57, some c507, some c41, some c300, some c297, some c524, some c45, some c202, some c246, some c216, some c28, some c212, some c531, some c29, some c204, some c309, some c265, some c335, some c66, some c317, some c275, some c361, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c530, c526, c506, c453, c385, c64, c57, c507, c41, c300, c297, c524, c45, c202, c246, c216, c28, c212, c531, c29, c204, c309, c265, c335, c66, c317, c275, c361] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c526 := derived526 a h
  have h2 : Entails.eval a c506 := derived506 a h
  have h3 : Entails.eval a c453 := derived453 a h
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c507 := derived507 a h
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c300 := h 299 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c524 := derived524 a h
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c212 := h 211 (by decide)
  have h18 : Entails.eval a c531 := derived531 a h
  have h19 : Entails.eval a c29 := h 28 (by decide)
  have h20 : Entails.eval a c204 := h 203 (by decide)
  have h21 : Entails.eval a c309 := h 308 (by decide)
  have h22 : Entails.eval a c265 := h 264 (by decide)
  have h23 : Entails.eval a c335 := h 334 (by decide)
  have h24 : Entails.eval a c66 := h 65 (by decide)
  have h25 : Entails.eval a c317 := h 316 (by decide)
  have h26 : Entails.eval a c275 := h 274 (by decide)
  have h27 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c453, some c385, some c381, some c530, some c532, some c344, some c341, some c40, some c56, some c467, some c301, some c46, some c265, some c291, some c303, some c66, some c258, some c312, some c346, some c65, some c356, some c481, some c319, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c506, c453, c385, c381, c530, c532, c344, c341, c40, c56, c467, c301, c46, c265, c291, c303, c66, c258, c312, c346, c65, c356, c481, c319] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c453 := derived453 a h
  have h2 : Entails.eval a c385 := h 384 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c530 := derived530 a h
  have h5 : Entails.eval a c532 := derived532 a h
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c341 := h 340 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c467 := derived467 a h
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c46 := h 45 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c303 := h 302 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  have h20 : Entails.eval a c65 := h 64 (by decide)
  have h21 : Entails.eval a c356 := h 355 (by decide)
  have h22 : Entails.eval a c481 := derived481 a h
  have h23 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c381, some c65, some c64, some c344, some c341, some c316, some c467, some c76, some c483, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c55, c381, c65, c64, c344, c341, c316, c467, c76, c483] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c381 := h 380 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c467 := derived467 a h
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c483 := derived483 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c526, some c506, some c453, some c385, some c381, some c533, some c103, some c97, some c42, some c65, some c84, some c55, some c534, some c104, some c62, some c347, some c314, some c36, some c81, some c475, some c276, some c66, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c526, c506, c453, c385, c381, c533, c103, c97, c42, c65, c84, c55, c534, c104, c62, c347, c314, c36, c81, c475, c276, c66] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c526 := derived526 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c533 := derived533 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c534 := derived534 a h
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c347 := h 346 (by decide)
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c475 := derived475 a h
  have h20 : Entails.eval a c276 := h 275 (by decide)
  have h21 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c97, some c42, some c65, some c84, some c55, some c444, some c66, some c293, some c36, some c347, some c62, some c104, some c64, some c76, some c316, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c103, c97, c42, c65, c84, c55, c444, c66, c293, c36, c347, c62, c104, c64, c76, c316] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c444 := derived444 a h
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c147, some c356, some c2, some c516, some c170, some c68, some c3, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c65, c147, c356, c2, c516, c170, c68, c3] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c516 := derived516 a h
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c444, some c75, some c76, some c371, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c537, c444, c75, c76, c371] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c444 := derived444 a h
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨47, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c186, some c158, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c183, c186, c158] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨50, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c293, some c45, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c301, c293, c45] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨44, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c270, some c50, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c271, c270, c50] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨44, by decide⟩, false), (⟨46, by decide⟩, false), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c541, some c258, some c315, some c314, some c61, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c541, c258, c315, c314, c61] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c541 := derived541 a h
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨7, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c98, some c84, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c104, c98, c84] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c526, some c506, some c453, some c385, some c381, some c535, some c536, some c538, some c543, some c68, some c439, some c66, some c75, some c540, some c542, some c65, some c147, some c356, some c436, some c5, some c376, some c158, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c526, c506, c453, c385, c381, c535, c536, c538, c543, c68, c439, c66, c75, c540, c542, c65, c147, c356, c436, c5, c376, c158] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c526 := derived526 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c535 := derived535 a h
  have h6 : Entails.eval a c536 := derived536 a h
  have h7 : Entails.eval a c538 := derived538 a h
  have h8 : Entails.eval a c543 := derived543 a h
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c439 := derived439 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c540 := derived540 a h
  have h14 : Entails.eval a c542 := derived542 a h
  have h15 : Entails.eval a c65 := h 64 (by decide)
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c356 := h 355 (by decide)
  have h18 : Entails.eval a c436 := derived436 a h
  have h19 : Entails.eval a c5 := h 4 (by decide)
  have h20 : Entails.eval a c376 := h 375 (by decide)
  have h21 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨24, by decide⟩, false), (⟨52, by decide⟩, false), (⟨34, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c242, some c188, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c475, c242, c188] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c242 := h 241 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c385, some c453, some c506, some c526, some c544, some c95, some c100, some c65, some c84, some c55, some c42, some c101, some c454, some c301, some c62, some c314, some c349, some c347, some c68, some c81, some c507, some c508, some c545, some c148, some c276, some c225, some c188, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c381, c385, c453, c506, c526, c544, c95, c100, c65, c84, c55, c42, c101, c454, c301, c62, c314, c349, c347, c68, c81, c507, c508, c545, c148, c276, c225, c188] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c506 := derived506 a h
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c544 := derived544 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c454 := derived454 a h
  have h14 : Entails.eval a c301 := h 300 (by decide)
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c314 := h 313 (by decide)
  have h17 : Entails.eval a c349 := h 348 (by decide)
  have h18 : Entails.eval a c347 := h 346 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c81 := h 80 (by decide)
  have h21 : Entails.eval a c507 := derived507 a h
  have h22 : Entails.eval a c508 := derived508 a h
  have h23 : Entails.eval a c545 := derived545 a h
  have h24 : Entails.eval a c148 := h 147 (by decide)
  have h25 : Entails.eval a c276 := h 275 (by decide)
  have h26 : Entails.eval a c225 := h 224 (by decide)
  have h27 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨34, by decide⟩, true), (⟨32, by decide⟩, false), (⟨33, by decide⟩, false), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c276, some c374, some c365, some c315, some c284, some c259, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c276, c374, c365, c315, c284, c259] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨30, by decide⟩, true), (⟨48, by decide⟩, false), (⟨34, by decide⟩, true), (⟨39, by decide⟩, true), (⟨32, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c386, some c380, some c95, some c65, some c547, some c84, some c101, some c260, some c188, some c259, some c297, some c23, some c315, some c348, some c50, some c152, some c358, some c189, some c10, some c382, some c278, some c149, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c546, c386, c380, c95, c65, c547, c84, c101, c260, c188, c259, c297, c23, c315, c348, c50, c152, c358, c189, c10, c382, c278, c149] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c547 := derived547 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c259 := h 258 (by decide)
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c315 := h 314 (by decide)
  have h14 : Entails.eval a c348 := h 347 (by decide)
  have h15 : Entails.eval a c50 := h 49 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c10 := h 9 (by decide)
  have h20 : Entails.eval a c382 := h 381 (by decide)
  have h21 : Entails.eval a c278 := h 277 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨36, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c65, some c314, some c84, some c148, some c358, some c8, some c6, some c369, some c166, some c159, some c133, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c95, c65, c314, c84, c148, c358, c8, c6, c369, c166, c159, c133] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c159 := h 158 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c386, some c380, some c546, some c95, some c100, some c65, some c84, some c55, some c42, some c101, some c62, some c314, some c349, some c347, some c81, some c547, some c549, some c475, some c260, some c188, some c548, some c297, some c23, some c240, some c310, some c199, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c386, c380, c546, c95, c100, c65, c84, c55, c42, c101, c62, c314, c349, c347, c81, c547, c549, c475, c260, c188, c548, c297, c23, c240, c310, c199] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c386 := h 385 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c547 := derived547 a h
  have h16 : Entails.eval a c549 := derived549 a h
  have h17 : Entails.eval a c475 := derived475 a h
  have h18 : Entails.eval a c260 := h 259 (by decide)
  have h19 : Entails.eval a c188 := h 187 (by decide)
  have h20 : Entails.eval a c548 := derived548 a h
  have h21 : Entails.eval a c297 := h 296 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c240 := h 239 (by decide)
  have h24 : Entails.eval a c310 := h 309 (by decide)
  have h25 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c81, some c278, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c42, c81, c278] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c435, some c358, some c369, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c435, c358, c369] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c435 := derived435 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c550, some c77, some c386, some c382, some c89, some c102, some c62, some c551, some c475, some c47, some c341, some c335, some c260, some c297, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c550, c77, c386, c382, c89, c102, c62, c551, c475, c47, c341, c335, c260, c297] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c551 := derived551 a h
  have h8 : Entails.eval a c475 := derived475 a h
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c341 := h 340 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c260 := h 259 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c550, some c386, some c380, some c546, some c77, some c553, some c552, some c367, some c372, some c65, some c147, some c421, some c81, some c168, some c102, some c4, some c93, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c550, c386, c380, c546, c77, c553, c552, c367, c372, c65, c147, c421, c81, c168, c102, c4, c93] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c553 := derived553 a h
  have h6 : Entails.eval a c552 := derived552 a h
  have h7 : Entails.eval a c367 := h 366 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c421 := derived421 a h
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨43, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c373, some c356, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c367, c373, c356] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c550, some c386, some c380, some c546, some c555, some c552, some c382, some c89, some c102, some c42, some c62, some c475, some c341, some c335, some c260, some c64, some c297, some c511, some c47, some c310, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c554, c550, c386, c380, c546, c555, c552, c382, c89, c102, c42, c62, c475, c341, c335, c260, c64, c297, c511, c47, c310] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c550 := derived550 a h
  have h2 : Entails.eval a c386 := h 385 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c546 := derived546 a h
  have h5 : Entails.eval a c555 := derived555 a h
  have h6 : Entails.eval a c552 := derived552 a h
  have h7 : Entails.eval a c382 := h 381 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c475 := derived475 a h
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c335 := h 334 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c64 := h 63 (by decide)
  have h17 : Entails.eval a c297 := h 296 (by decide)
  have h18 : Entails.eval a c511 := derived511 a h
  have h19 : Entails.eval a c47 := h 46 (by decide)
  have h20 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨41, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c62, some c295, some c341, some c314, some c47, some c55, some c297, some c270, some c193, some c187, some c22, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c42, c62, c295, c341, c314, c47, c55, c297, c270, c193, c187, c22] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c550, some c556, some c67, some c554, some c386, some c380, some c546, some c370, some c79, some c557, some c102, some c84, some c93, some c99, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c550, c556, c67, c554, c386, c380, c546, c370, c79, c557, c102, c84, c93, c99] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c554 := derived554 a h
  have h4 : Entails.eval a c386 := h 385 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c557 := derived557 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c550, some c386, some c380, some c554, some c556, some c67, some c382, some c558, some c356, some c435, some c373, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c550, c386, c380, c554, c556, c67, c382, c558, c356, c435, c373] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c554 := derived554 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c558 := derived558 a h
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c435 := derived435 a h
  have h10 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c386, some c559, some c96, some c101, some c84, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c380, c386, c559, c96, c101, c84] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c386 := h 385 (by decide)
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨41, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c323, some c54, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c314, c323, c54] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c323 := h 322 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨3, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c299, some c295, some c48, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c299, c295, c48] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c299 := h 298 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c65, some c78, some c561, some c562, some c265, some c270, some c279, some c43, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c84, c65, c78, c561, c562, c265, c270, c279, c43] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c562 := derived562 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c270 := h 269 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c101, some c84, some c384, some c65, some c368, some c552, some c148, some c358, some c445, some c563, some c100, some c42, some c55, some c299, some c314, some c315, some c43, some c271, some c270, some c264, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c96, c101, c84, c384, c65, c368, c552, c148, c358, c445, c563, c100, c42, c55, c299, c314, c315, c43, c271, c270, c264] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c552 := derived552 a h
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c445 := derived445 a h
  have h10 : Entails.eval a c563 := derived563 a h
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  have h14 : Entails.eval a c299 := h 298 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c315 := h 314 (by decide)
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c271 := h 270 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨41, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c55, some c299, some c312, some c315, some c43, some c271, some c268, some c259, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c42, c55, c299, c312, c315, c43, c271, c268, c259] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c271 := h 270 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c96, some c65, some c84, some c384, some c564, some c150, some c363, some c422, some c371, some c369, some c168, some c148, some c565, some c100, some c78, some c79, some c374, some c13, some c161, some c165, some c185, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c101, c96, c65, c84, c384, c564, c150, c363, c422, c371, c369, c168, c148, c565, c100, c78, c79, c374, c13, c161, c165, c185] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c564 := derived564 a h
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c422 := derived422 a h
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c369 := h 368 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c565 := derived565 a h
  have h14 : Entails.eval a c100 := h 99 (by decide)
  have h15 : Entails.eval a c78 := h 77 (by decide)
  have h16 : Entails.eval a c79 := h 78 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨46, by decide⟩, false), (⟨12, by decide⟩, false), (⟨42, by decide⟩, false), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c371, some c78, some c79, some c374, some c13, some c161, some c165, some c185, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c367, c371, c78, c79, c374, c13, c161, c165, c185] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c374 := h 373 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨48, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c179, some c156, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c185, c179, c156] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c43, some c286, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c48, c43, c286] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c342, some c54, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c333, c342, c54] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c342 := h 341 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c289, some c298, some c43, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c289, c298, c43] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c289 := h 288 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c570, some c571, some c41, some c193, some c267, some c247, some c299, some c48, some c310, some c52, some c204, some c33, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c570, c571, c41, c193, c267, c247, c299, c48, c310, c52, c204, c33] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c570 := derived570 a h
  have h1 : Entails.eval a c571 := derived571 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨37, by decide⟩, false), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨45, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c193, some c352, some c319, some c30, some c190, some c148, some c279, some c422, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c260, c193, c352, c319, c30, c190, c148, c279, c422] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c193 := h 192 (by decide)
  have h2 : Entails.eval a c352 := h 351 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c422 := derived422 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨33, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨50, by decide⟩, true), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c96, some c54, some c35, some c289, some c573, some c355, some c55, some c238, some c30, some c207, some c190, some c26, some c279, some c188, some c422, some c319, some c148, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c101, c96, c54, c35, c289, c573, c355, c55, c238, c30, c207, c190, c26, c279, c188, c422, c319, c148] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c573 := derived573 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c238 := h 237 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c279 := h 278 (by decide)
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c422 := derived422 a h
  have h16 : Entails.eval a c319 := h 318 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c101, some c546, some c560, some c566, some c572, some c89, some c569, some c382, some c69, some c295, some c309, some c37, some c330, some c55, some c54, some c35, some c289, some c49, some c573, some c355, some c574, some c198, some c24, some c26, some c214, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c96, c101, c546, c560, c566, c572, c89, c569, c382, c69, c295, c309, c37, c330, c55, c54, c35, c289, c49, c573, c355, c574, c198, c24, c26, c214] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c560 := derived560 a h
  have h4 : Entails.eval a c566 := derived566 a h
  have h5 : Entails.eval a c572 := derived572 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c569 := derived569 a h
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c309 := h 308 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c330 := h 329 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c35 := h 34 (by decide)
  have h17 : Entails.eval a c289 := h 288 (by decide)
  have h18 : Entails.eval a c49 := h 48 (by decide)
  have h19 : Entails.eval a c573 := derived573 a h
  have h20 : Entails.eval a c355 := h 354 (by decide)
  have h21 : Entails.eval a c574 := derived574 a h
  have h22 : Entails.eval a c198 := h 197 (by decide)
  have h23 : Entails.eval a c24 := h 23 (by decide)
  have h24 : Entails.eval a c26 := h 25 (by decide)
  have h25 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨19, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c101, some c569, some c267, some c333, some c54, some c35, some c355, some c286, some c265, some c49, some c201, some c303, some c574, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c96, c101, c569, c267, c333, c54, c35, c355, c286, c265, c49, c201, c303, c574] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c569 := derived569 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c303 := h 302 (by decide)
  have h13 : Entails.eval a c574 := derived574 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c560, some c566, some c101, some c96, some c572, some c69, some c89, some c382, some c569, some c575, some c42, some c194, some c26, some c244, some c576, some c289, some c311, some c35, some c265, some c330, some c347, some c59, some c188, some c323, some c275, some c422, some c148, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c546, c560, c566, c101, c96, c572, c69, c89, c382, c569, c575, c42, c194, c26, c244, c576, c289, c311, c35, c265, c330, c347, c59, c188, c323, c275, c422, c148] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c560 := derived560 a h
  have h2 : Entails.eval a c566 := derived566 a h
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c572 := derived572 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c569 := derived569 a h
  have h10 : Entails.eval a c575 := derived575 a h
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c244 := h 243 (by decide)
  have h15 : Entails.eval a c576 := derived576 a h
  have h16 : Entails.eval a c289 := h 288 (by decide)
  have h17 : Entails.eval a c311 := h 310 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  have h20 : Entails.eval a c330 := h 329 (by decide)
  have h21 : Entails.eval a c347 := h 346 (by decide)
  have h22 : Entails.eval a c59 := h 58 (by decide)
  have h23 : Entails.eval a c188 := h 187 (by decide)
  have h24 : Entails.eval a c323 := h 322 (by decide)
  have h25 : Entails.eval a c275 := h 274 (by decide)
  have h26 : Entails.eval a c422 := derived422 a h
  have h27 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨33, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c295, some c330, some c261, some c189, some c347, some c23, some c188, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c295, c330, c261, c189, c347, c23, c188] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c295 := h 294 (by decide)
  have h1 : Entails.eval a c330 := h 329 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c363, some c360, some c369, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c363, c360, c369] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c363 := h 362 (by decide)
  have h1 : Entails.eval a c360 := h 359 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c148, some c358, some c445, some c369, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c148, c358, c445, c369] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c148 := h 147 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c445 := derived445 a h
  have h3 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨33, by decide⟩, false), (⟨32, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c101, some c96, some c546, some c289, some c571, some c43, some c69, some c282, some c309, some c311, some c74, some c578, some c444, some c579, some c580, some c561, some c329, some c190, some c188, some c24, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c100, c101, c96, c546, c289, c571, c43, c69, c282, c309, c311, c74, c578, c444, c579, c580, c561, c329, c190, c188, c24] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c571 := derived571 a h
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c74 := h 73 (by decide)
  have h12 : Entails.eval a c578 := derived578 a h
  have h13 : Entails.eval a c444 := derived444 a h
  have h14 : Entails.eval a c579 := derived579 a h
  have h15 : Entails.eval a c580 := derived580 a h
  have h16 : Entails.eval a c561 := derived561 a h
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c188 := h 187 (by decide)
  have h20 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨20, by decide⟩, true), (⟨31, by decide⟩, true), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c42, some c260, some c347, some c346, some c214, some c210, some c263, some c23, some c256, some c310, some c197, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c100, c42, c260, c347, c346, c214, c210, c263, c23, c256, c310, c197] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c546, some c96, some c101, some c566, some c577, some c100, some c42, some c55, some c333, some c64, some c581, some c193, some c30, some c582, some c309, some c307, some c43, some c263, some c303, some c348, some c346, some c199, some c23, some c208, some c27, some c70, some c52, some c284, some c271, some c74, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c560, c546, c96, c101, c566, c577, c100, c42, c55, c333, c64, c581, c193, c30, c582, c309, c307, c43, c263, c303, c348, c346, c199, c23, c208, c27, c70, c52, c284, c271, c74] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c566 := derived566 a h
  have h5 : Entails.eval a c577 := derived577 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c581 := derived581 a h
  have h12 : Entails.eval a c193 := h 192 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c582 := derived582 a h
  have h15 : Entails.eval a c309 := h 308 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c263 := h 262 (by decide)
  have h19 : Entails.eval a c303 := h 302 (by decide)
  have h20 : Entails.eval a c348 := h 347 (by decide)
  have h21 : Entails.eval a c346 := h 345 (by decide)
  have h22 : Entails.eval a c199 := h 198 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  have h24 : Entails.eval a c208 := h 207 (by decide)
  have h25 : Entails.eval a c27 := h 26 (by decide)
  have h26 : Entails.eval a c70 := h 69 (by decide)
  have h27 : Entails.eval a c52 := h 51 (by decide)
  have h28 : Entails.eval a c284 := h 283 (by decide)
  have h29 : Entails.eval a c271 := h 270 (by decide)
  have h30 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c560, some c583, some c68, some c55, some c62, some c314, some c74, some c349, some c64, some c546, some c91, some c293, some c494, some c307, some c276, some c148, some c358, some c375, some c284, some c445, some c330, some c189, some c263, some c244, some c27, some c289, some c216, some c204, some c43, some c31, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c100, c560, c583, c68, c55, c62, c314, c74, c349, c64, c546, c91, c293, c494, c307, c276, c148, c358, c375, c284, c445, c330, c189, c263, c244, c27, c289, c216, c204, c43, c31] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c560 := derived560 a h
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c349 := h 348 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c546 := derived546 a h
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c494 := derived494 a h
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c276 := h 275 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c375 := h 374 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c445 := derived445 a h
  have h21 : Entails.eval a c330 := h 329 (by decide)
  have h22 : Entails.eval a c189 := h 188 (by decide)
  have h23 : Entails.eval a c263 := h 262 (by decide)
  have h24 : Entails.eval a c244 := h 243 (by decide)
  have h25 : Entails.eval a c27 := h 26 (by decide)
  have h26 : Entails.eval a c289 := h 288 (by decide)
  have h27 : Entails.eval a c216 := h 215 (by decide)
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c43 := h 42 (by decide)
  have h30 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨18, by decide⟩, false), (⟨48, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c583, some c100, some c62, some c349, some c546, some c560, some c91, some c189, some c212, some c295, some c278, some c238, some c445, some c149, some c10, some c125, some c168, some c173, some c242, some c133, some c106, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c23, c583, c100, c62, c349, c546, c560, c91, c189, c212, c295, c278, c238, c445, c149, c10, c125, c168, c173, c242, c133, c106] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c583 := derived583 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c349 := h 348 (by decide)
  have h5 : Entails.eval a c546 := derived546 a h
  have h6 : Entails.eval a c560 := derived560 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c278 := h 277 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c445 := derived445 a h
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c125 := h 124 (by decide)
  have h17 : Entails.eval a c168 := h 167 (by decide)
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c242 := h 241 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  have h21 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c583, some c68, some c546, some c91, some c100, some c62, some c55, some c349, some c347, some c314, some c64, some c74, some c584, some c188, some c23, some c585, some c330, some c348, some c259, some c284, some c152, some c16, some c131, some c10, some c111, some c170, some c149, some c238, some c133, some c372, some c106, some c358, some c242, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c560, c583, c68, c546, c91, c100, c62, c55, c349, c347, c314, c64, c74, c584, c188, c23, c585, c330, c348, c259, c284, c152, c16, c131, c10, c111, c170, c149, c238, c133, c372, c106, c358, c242] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c583 := derived583 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c349 := h 348 (by decide)
  have h9 : Entails.eval a c347 := h 346 (by decide)
  have h10 : Entails.eval a c314 := h 313 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c584 := derived584 a h
  have h14 : Entails.eval a c188 := h 187 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c585 := derived585 a h
  have h17 : Entails.eval a c330 := h 329 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c259 := h 258 (by decide)
  have h20 : Entails.eval a c284 := h 283 (by decide)
  have h21 : Entails.eval a c152 := h 151 (by decide)
  have h22 : Entails.eval a c16 := h 15 (by decide)
  have h23 : Entails.eval a c131 := h 130 (by decide)
  have h24 : Entails.eval a c10 := h 9 (by decide)
  have h25 : Entails.eval a c111 := h 110 (by decide)
  have h26 : Entails.eval a c170 := h 169 (by decide)
  have h27 : Entails.eval a c149 := h 148 (by decide)
  have h28 : Entails.eval a c238 := h 237 (by decide)
  have h29 : Entails.eval a c133 := h 132 (by decide)
  have h30 : Entails.eval a c372 := h 371 (by decide)
  have h31 : Entails.eval a c106 := h 105 (by decide)
  have h32 : Entails.eval a c358 := h 357 (by decide)
  have h33 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c583, some c68, some c586, some c88, some c295, some c37, some c47, some c330, some c55, some c35, some c102, some c270, some c73, some c569, some c279, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c560, c583, c68, c586, c88, c295, c37, c47, c330, c55, c35, c102, c270, c73, c569, c279] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c583 := derived583 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c330 := h 329 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c569 := derived569 a h
  have h15 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c583, some c68, some c587, some c42, some c100, some c102, some c88, some c572, some c569, some c69, some c279, some c38, some c323, some c59, some c54, some c330, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c560, c583, c68, c587, c42, c100, c102, c88, c572, c569, c69, c279, c38, c323, c59, c54, c330] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c583 := derived583 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c587 := derived587 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c572 := derived572 a h
  have h9 : Entails.eval a c569 := derived569 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c279 := h 278 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c323 := h 322 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c330, some c60, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c333, c330, c60] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c330 := h 329 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c286, some c289, some c49, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c286, c289, c49] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c286 := h 285 (by decide)
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c560, some c583, some c91, some c588, some c95, some c99, some c88, some c589, some c590, some c258, some c295, some c47, some c49, some c311, some c48, some c257, some c102, some c62, some c64, some c355, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c546, c560, c583, c91, c588, c95, c99, c88, c589, c590, c258, c295, c47, c49, c311, c48, c257, c102, c62, c64, c355] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c560 := derived560 a h
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c588 := derived588 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c589 := derived589 a h
  have h9 : Entails.eval a c590 := derived590 a h
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c311 := h 310 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c102 := h 101 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨50, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c47, some c49, some c311, some c280, some c48, some c79, some c102, some c552, some c83, some c372, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c47, c49, c311, c280, c48, c79, c102, c552, c83, c372] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c47 := h 46 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c311 := h 310 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c552 := derived552 a h
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c304, some c302, some c197, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c304, c302, c197] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c304 := h 303 (by decide)
  have h1 : Entails.eval a c302 := h 301 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c346, some c58, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c347, c346, c58] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, true), (⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c91, some c95, some c99, some c88, some c382, some c592, some c295, some c42, some c194, some c26, some c34, some c593, some c258, some c594, some c208, some c350, some c348, some c60, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c68, c91, c95, c99, c88, c382, c592, c295, c42, c194, c26, c34, c593, c258, c594, c208, c350, c348, c60] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c593 := derived593 a h
  have h13 : Entails.eval a c258 := h 257 (by decide)
  have h14 : Entails.eval a c594 := derived594 a h
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c350 := h 349 (by decide)
  have h17 : Entails.eval a c348 := h 347 (by decide)
  have h18 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨44, by decide⟩, false), (⟨4, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c55, some c314, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c62, c55, c314] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c560, some c583, some c68, some c591, some c595, some c65, some c368, some c596, some c100, some c102, some c88, some c563, some c382, some c552, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c546, c560, c583, c68, c591, c595, c65, c368, c596, c100, c102, c88, c563, c382, c552] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c560 := derived560 a h
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c591 := derived591 a h
  have h5 : Entails.eval a c595 := derived595 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c596 := derived596 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c563 := derived563 a h
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c552 := derived552 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c597, some c100, some c102, some c84, some c386, some c343, some c88, some c59, some c339, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c597, c100, c102, c84, c386, c343, c88, c59, c339] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c597 := derived597 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c386 := h 385 (by decide)
  have h5 : Entails.eval a c343 := h 342 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨32, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨40, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c343, some c299, some c39, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c84, c343, c299, c39] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨37, by decide⟩, true), (⟨32, by decide⟩, false), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c384, some c299, some c580, some c339, some c295, some c262, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c384, c299, c580, c339, c295, c262] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c384 := h 383 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c580 := derived580 a h
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c339, some c295, some c262, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c339, c295, c262] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c339 := h 338 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨5, by decide⟩, false), (⟨32, by decide⟩, false), (⟨42, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c25, some c601, some c580, some c337, some c293, some c188, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c191, c25, c601, c580, c337, c293, c188] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c601 := derived601 a h
  have h3 : Entails.eval a c580 := derived580 a h
  have h4 : Entails.eval a c337 := h 336 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨53, by decide⟩, true), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c173, some c175, some c539, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c173, c175, c539] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c173 := h 172 (by decide)
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c539 := derived539 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨37, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c370, some c368, some c603, some c91, some c88, some c580, some c454, some c337, some c158, some c188, some c23, some c25, some c211, some c16, some c10, some c83, some c149, some c322, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c68, c370, c368, c603, c91, c88, c580, c454, c337, c158, c188, c23, c25, c211, c16, c10, c83, c149, c322] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c603 := derived603 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c580 := derived580 a h
  have h7 : Entails.eval a c454 := derived454 a h
  have h8 : Entails.eval a c337 := h 336 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨5, by decide⟩, false), (⟨32, by decide⟩, false), (⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c368, some c370, some c600, some c602, some c494, some c603, some c604, some c382, some c339, some c295, some c552, some c148, some c37, some c8, some c6, some c166, some c161, some c181, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c68, c368, c370, c600, c602, c494, c603, c604, c382, c339, c295, c552, c148, c37, c8, c6, c166, c161, c181] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c602 := derived602 a h
  have h5 : Entails.eval a c494 := derived494 a h
  have h6 : Entails.eval a c603 := derived603 a h
  have h7 : Entails.eval a c604 := derived604 a h
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c339 := h 338 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c552 := derived552 a h
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c166 := h 165 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨2, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c539, some c148, some c170, some c382, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c8, c539, c148, c170, c382] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c539 := derived539 a h
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, false), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c603, some c606, some c171, some c166, some c382, some c181, some c552, some c161, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c603, c606, c171, c166, c382, c181, c552, c161] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c552 := derived552 a h
  have h7 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨8, by decide⟩, true), (⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c65, some c91, some c68, some c370, some c368, some c447, some c599, some c605, some c343, some c603, some c607, some c10, some c179, some c88, some c166, some c382, some c8, some c148, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c65, c91, c68, c370, c368, c447, c599, c605, c343, c603, c607, c10, c179, c88, c166, c382, c8, c148] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c447 := derived447 a h
  have h6 : Entails.eval a c599 := derived599 a h
  have h7 : Entails.eval a c605 := derived605 a h
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c603 := derived603 a h
  have h10 : Entails.eval a c607 := derived607 a h
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c179 := h 178 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c166 := h 165 (by decide)
  have h15 : Entails.eval a c382 := h 381 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨10, by decide⟩, true), (⟨42, by decide⟩, true), (⟨47, by decide⟩, true), (⟨55, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨52, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c460, some c158, some c79, some c14, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c460, c158, c79, c14] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c460 := derived460 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨13, by decide⟩, true), (⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c166, some c179, some c181, some c171, some c161, some c382, some c552, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c166, c179, c181, c171, c161, c382, c552] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c166 := h 165 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c382 := h 381 (by decide)
  have h6 : Entails.eval a c552 := derived552 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, false), (⟨42, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c610, some c175, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c610, c175] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c610 := derived610 a h
  have h1 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨42, by decide⟩, true), (⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c370, some c365, some c81, some c326, some c282, some c602, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c371, c370, c365, c81, c326, c282, c602] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c370 := h 369 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c602 := derived602 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c612, some c611, some c8, some c539, some c148, some c337, some c475, some c545, some c188, some c240, some c113, some c145, some c129, some c602, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c612, c611, c8, c539, c148, c337, c475, c545, c188, c240, c113, c145, c129, c602] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c612 := derived612 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c475 := derived475 a h
  have h7 : Entails.eval a c545 := derived545 a h
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c240 := h 239 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c129 := h 128 (by decide)
  have h13 : Entails.eval a c602 := derived602 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨5, by decide⟩, false), (⟨56, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c367, some c368, some c77, some c81, some c320, some c276, some c374, some c188, some c361, some c23, some c339, some c295, some c189, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c613, c367, c368, c77, c81, c320, c276, c374, c188, c361, c23, c339, c295, c189] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨26, by decide⟩, true), (⟨48, by decide⟩, false), (⟨25, by decide⟩, false), (⟨53, by decide⟩, true), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c374, some c365, some c328, some c271, some c259, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c320, c374, c365, c328, c271, c259] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c271 := h 270 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨34, by decide⟩, true), (⟨26, by decide⟩, true), (⟨48, by decide⟩, false), (⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c328, some c271, some c259, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c328, c271, c259] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c328 := h 327 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨31, by decide⟩, true), (⟨48, by decide⟩, false), (⟨25, by decide⟩, false), (⟨5, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨40, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c614, some c51, some c303, some c615, some c53, some c260, some c188, some c25, some c616, some c70, some c152, some c358, some c365, some c16, some c382, some c545, some c326, some c454, some c205, some c158, some c221, some c316, some c206, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c614, c51, c303, c615, c53, c260, c188, c25, c616, c70, c152, c358, c365, c16, c382, c545, c326, c454, c205, c158, c221, c316, c206] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c614 := derived614 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c303 := h 302 (by decide)
  have h3 : Entails.eval a c615 := derived615 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c616 := derived616 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c365 := h 364 (by decide)
  have h13 : Entails.eval a c16 := h 15 (by decide)
  have h14 : Entails.eval a c382 := h 381 (by decide)
  have h15 : Entails.eval a c545 := derived545 a h
  have h16 : Entails.eval a c326 := h 325 (by decide)
  have h17 : Entails.eval a c454 := derived454 a h
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c158 := h 157 (by decide)
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c316 := h 315 (by decide)
  have h22 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c597, some c546, some c65, some c598, some c608, some c386, some c84, some c614, some c447, some c51, some c44, some c81, some c297, some c303, some c615, some c617, some c337, some c358, some c148, some c371, some c8, some c611, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c597, c546, c65, c598, c608, c386, c84, c614, c447, c51, c44, c81, c297, c303, c615, c617, c337, c358, c148, c371, c8, c611] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c597 := derived597 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c598 := derived598 a h
  have h4 : Entails.eval a c608 := derived608 a h
  have h5 : Entails.eval a c386 := h 385 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c614 := derived614 a h
  have h8 : Entails.eval a c447 := derived447 a h
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c303 := h 302 (by decide)
  have h14 : Entails.eval a c615 := derived615 a h
  have h15 : Entails.eval a c617 := derived617 a h
  have h16 : Entails.eval a c337 := h 336 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c371 := h 370 (by decide)
  have h20 : Entails.eval a c8 := h 7 (by decide)
  have h21 : Entails.eval a c611 := derived611 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived618

end CochromaticTwenty.Certificates.B16_8_0Enumerating
