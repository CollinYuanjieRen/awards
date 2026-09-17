import MerLeanExperiment.Certificates.Z12Direct_5_7_7.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_7_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_7_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c323 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f323 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c287, some c322, some c51, some c215, some c168, some c102, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p323 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked323 : lratChecker f323 p323 = .success := by decide +kernel
theorem unsat323 : Unsatisfiable (PosFin 31) f323 := by
  apply lratCheckerSound f323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p323
  · intro a ha; simp [p323] at ha; subst a; trivial
  · exact checked323
theorem derived323 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c323 := by
  apply localUnsat_implies_entails f323 [c287, c322, c51, c215, c168, c102] c323 unsat323 (by rfl) a
  have h0 : Entails.eval a c287 := derived287 a h
  have h1 : Entails.eval a c322 := derived322 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c324 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f324 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c287, some c322, some c289, some c323, some c28, some c168, some c153, some c104, some c122, some c34, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p324 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked324 : lratChecker f324 p324 = .success := by decide +kernel
theorem unsat324 : Unsatisfiable (PosFin 31) f324 := by
  apply lratCheckerSound f324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p324
  · intro a ha; simp [p324] at ha; subst a; trivial
  · exact checked324
theorem derived324 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c324 := by
  apply localUnsat_implies_entails f324 [c287, c322, c289, c323, c28, c168, c153, c104, c122, c34] c324 unsat324 (by rfl) a
  have h0 : Entails.eval a c287 := derived287 a h
  have h1 : Entails.eval a c322 := derived322 a h
  have h2 : Entails.eval a c289 := derived289 a h
  have h3 : Entails.eval a c323 := derived323 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c325 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f325 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c324, some c287, some c316, some c289, some c198, some c30, some c201, some c28, some c154, some c172, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p325 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked325 : lratChecker f325 p325 = .success := by decide +kernel
theorem unsat325 : Unsatisfiable (PosFin 31) f325 := by
  apply lratCheckerSound f325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p325
  · intro a ha; simp [p325] at ha; subst a; trivial
  · exact checked325
theorem derived325 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c325 := by
  apply localUnsat_implies_entails f325 [c324, c287, c316, c289, c198, c30, c201, c28, c154, c172] c325 unsat325 (by rfl) a
  have h0 : Entails.eval a c324 := derived324 a h
  have h1 : Entails.eval a c287 := derived287 a h
  have h2 : Entails.eval a c316 := derived316 a h
  have h3 : Entails.eval a c289 := derived289 a h
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c326 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f326 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c325, some c324, some c287, some c137, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p326 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked326 : lratChecker f326 p326 = .success := by decide +kernel
theorem unsat326 : Unsatisfiable (PosFin 31) f326 := by
  apply lratCheckerSound f326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p326
  · intro a ha; simp [p326] at ha; subst a; trivial
  · exact checked326
theorem derived326 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c326 := by
  apply localUnsat_implies_entails f326 [c325, c324, c287, c137] c326 unsat326 (by rfl) a
  have h0 : Entails.eval a c325 := derived325 a h
  have h1 : Entails.eval a c324 := derived324 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c327 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f327 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c287, some c324, some c316, some c326, some c120, some c106, some c30, some c201, some c154, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p327 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked327 : lratChecker f327 p327 = .success := by decide +kernel
theorem unsat327 : Unsatisfiable (PosFin 31) f327 := by
  apply lratCheckerSound f327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p327
  · intro a ha; simp [p327] at ha; subst a; trivial
  · exact checked327
theorem derived327 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c327 := by
  apply localUnsat_implies_entails f327 [c287, c324, c316, c326, c120, c106, c30, c201, c154] c327 unsat327 (by rfl) a
  have h0 : Entails.eval a c287 := derived287 a h
  have h1 : Entails.eval a c324 := derived324 a h
  have h2 : Entails.eval a c316 := derived316 a h
  have h3 : Entails.eval a c326 := derived326 a h
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c328 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f328 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c316, some c326, some c325, some c324, some c34, some c187, some c25, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p328 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked328 : lratChecker f328 p328 = .success := by decide +kernel
theorem unsat328 : Unsatisfiable (PosFin 31) f328 := by
  apply lratCheckerSound f328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p328
  · intro a ha; simp [p328] at ha; subst a; trivial
  · exact checked328
theorem derived328 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c328 := by
  apply localUnsat_implies_entails f328 [c316, c326, c325, c324, c34, c187, c25] c328 unsat328 (by rfl) a
  have h0 : Entails.eval a c316 := derived316 a h
  have h1 : Entails.eval a c326 := derived326 a h
  have h2 : Entails.eval a c325 := derived325 a h
  have h3 : Entails.eval a c324 := derived324 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c329 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f329 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c324, some c287, some c120, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p329 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked329 : lratChecker f329 p329 = .success := by decide +kernel
theorem unsat329 : Unsatisfiable (PosFin 31) f329 := by
  apply lratCheckerSound f329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p329
  · intro a ha; simp [p329] at ha; subst a; trivial
  · exact checked329
theorem derived329 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c329 := by
  apply localUnsat_implies_entails f329 [c328, c324, c287, c120] c329 unsat329 (by rfl) a
  have h0 : Entails.eval a c328 := derived328 a h
  have h1 : Entails.eval a c324 := derived324 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c330 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f330 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c316, some c326, some c325, some c287, some c324, some c327, some c136, some c154, some c1, some c319, some c16, some c14, some c307, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p330 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked330 : lratChecker f330 p330 = .success := by decide +kernel
theorem unsat330 : Unsatisfiable (PosFin 31) f330 := by
  apply lratCheckerSound f330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p330
  · intro a ha; simp [p330] at ha; subst a; trivial
  · exact checked330
theorem derived330 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c330 := by
  apply localUnsat_implies_entails f330 [c328, c316, c326, c325, c287, c324, c327, c136, c154, c1, c319, c16, c14, c307] c330 unsat330 (by rfl) a
  have h0 : Entails.eval a c328 := derived328 a h
  have h1 : Entails.eval a c316 := derived316 a h
  have h2 : Entails.eval a c326 := derived326 a h
  have h3 : Entails.eval a c325 := derived325 a h
  have h4 : Entails.eval a c287 := derived287 a h
  have h5 : Entails.eval a c324 := derived324 a h
  have h6 : Entails.eval a c327 := derived327 a h
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c154 := h 153 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c319 := derived319 a h
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c307 := derived307 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c331 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f331 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c330, some c2, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p331 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked331 : lratChecker f331 p331 = .success := by decide +kernel
theorem unsat331 : Unsatisfiable (PosFin 31) f331 := by
  apply lratCheckerSound f331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p331
  · intro a ha; simp [p331] at ha; subst a; trivial
  · exact checked331
theorem derived331 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c331 := by
  apply localUnsat_implies_entails f331 [c328, c330, c2] c331 unsat331 (by rfl) a
  have h0 : Entails.eval a c328 := derived328 a h
  have h1 : Entails.eval a c330 := derived330 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c332 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f332 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c330, some c325, some c287, some c199, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p332 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked332 : lratChecker f332 p332 = .success := by decide +kernel
theorem unsat332 : Unsatisfiable (PosFin 31) f332 := by
  apply lratCheckerSound f332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p332
  · intro a ha; simp [p332] at ha; subst a; trivial
  · exact checked332
theorem derived332 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c332 := by
  apply localUnsat_implies_entails f332 [c330, c325, c287, c199] c332 unsat332 (by rfl) a
  have h0 : Entails.eval a c330 := derived330 a h
  have h1 : Entails.eval a c325 := derived325 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c333 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f333 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c330, some c328, some c287, some c28, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p333 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked333 : lratChecker f333 p333 = .success := by decide +kernel
theorem unsat333 : Unsatisfiable (PosFin 31) f333 := by
  apply lratCheckerSound f333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p333
  · intro a ha; simp [p333] at ha; subst a; trivial
  · exact checked333
theorem derived333 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c333 := by
  apply localUnsat_implies_entails f333 [c330, c328, c287, c28] c333 unsat333 (by rfl) a
  have h0 : Entails.eval a c330 := derived330 a h
  have h1 : Entails.eval a c328 := derived328 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c334 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f334 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c331, some c332, some c309, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p334 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked334 : lratChecker f334 p334 = .success := by decide +kernel
theorem unsat334 : Unsatisfiable (PosFin 31) f334 := by
  apply lratCheckerSound f334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p334
  · intro a ha; simp [p334] at ha; subst a; trivial
  · exact checked334
theorem derived334 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c334 := by
  apply localUnsat_implies_entails f334 [c331, c332, c309] c334 unsat334 (by rfl) a
  have h0 : Entails.eval a c331 := derived331 a h
  have h1 : Entails.eval a c332 := derived332 a h
  have h2 : Entails.eval a c309 := derived309 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c335 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f335 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c332, some c326, some c316, some c154, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p335 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked335 : lratChecker f335 p335 = .success := by decide +kernel
theorem unsat335 : Unsatisfiable (PosFin 31) f335 := by
  apply lratCheckerSound f335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p335
  · intro a ha; simp [p335] at ha; subst a; trivial
  · exact checked335
theorem derived335 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c335 := by
  apply localUnsat_implies_entails f335 [c332, c326, c316, c154] c335 unsat335 (by rfl) a
  have h0 : Entails.eval a c332 := derived332 a h
  have h1 : Entails.eval a c326 := derived326 a h
  have h2 : Entails.eval a c316 := derived316 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c336 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f336 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c335, some c325, some c1, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p336 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked336 : lratChecker f336 p336 = .success := by decide +kernel
theorem unsat336 : Unsatisfiable (PosFin 31) f336 := by
  apply lratCheckerSound f336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p336
  · intro a ha; simp [p336] at ha; subst a; trivial
  · exact checked336
theorem derived336 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c336 := by
  apply localUnsat_implies_entails f336 [c335, c325, c1] c336 unsat336 (by rfl) a
  have h0 : Entails.eval a c335 := derived335 a h
  have h1 : Entails.eval a c325 := derived325 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c337 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f337 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c336, some c333, some c294, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p337 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked337 : lratChecker f337 p337 = .success := by decide +kernel
theorem unsat337 : Unsatisfiable (PosFin 31) f337 := by
  apply lratCheckerSound f337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p337
  · intro a ha; simp [p337] at ha; subst a; trivial
  · exact checked337
theorem derived337 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c337 := by
  apply localUnsat_implies_entails f337 [c336, c333, c294] c337 unsat337 (by rfl) a
  have h0 : Entails.eval a c336 := derived336 a h
  have h1 : Entails.eval a c333 := derived333 a h
  have h2 : Entails.eval a c294 := derived294 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c338 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f338 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c336, some c319, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p338 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked338 : lratChecker f338 p338 = .success := by decide +kernel
theorem unsat338 : Unsatisfiable (PosFin 31) f338 := by
  apply lratCheckerSound f338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p338
  · intro a ha; simp [p338] at ha; subst a; trivial
  · exact checked338
theorem derived338 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c338 := by
  apply localUnsat_implies_entails f338 [c336, c319] c338 unsat338 (by rfl) a
  have h0 : Entails.eval a c336 := derived336 a h
  have h1 : Entails.eval a c319 := derived319 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c339 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f339 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c338, some c324, some c287, some c14, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p339 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked339 : lratChecker f339 p339 = .success := by decide +kernel
theorem unsat339 : Unsatisfiable (PosFin 31) f339 := by
  apply lratCheckerSound f339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p339
  · intro a ha; simp [p339] at ha; subst a; trivial
  · exact checked339
theorem derived339 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c339 := by
  apply localUnsat_implies_entails f339 [c338, c324, c287, c14] c339 unsat339 (by rfl) a
  have h0 : Entails.eval a c338 := derived338 a h
  have h1 : Entails.eval a c324 := derived324 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c340 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f340 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c338, some c337, some c330, some c328, some c332, some c320, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p340 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked340 : lratChecker f340 p340 = .success := by decide +kernel
theorem unsat340 : Unsatisfiable (PosFin 31) f340 := by
  apply lratCheckerSound f340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p340
  · intro a ha; simp [p340] at ha; subst a; trivial
  · exact checked340
theorem derived340 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c340 := by
  apply localUnsat_implies_entails f340 [c338, c337, c330, c328, c332, c320] c340 unsat340 (by rfl) a
  have h0 : Entails.eval a c338 := derived338 a h
  have h1 : Entails.eval a c337 := derived337 a h
  have h2 : Entails.eval a c330 := derived330 a h
  have h3 : Entails.eval a c328 := derived328 a h
  have h4 : Entails.eval a c332 := derived332 a h
  have h5 : Entails.eval a c320 := derived320 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c341 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f341 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c339, some c331, some c326, some c96, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p341 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked341 : lratChecker f341 p341 = .success := by decide +kernel
theorem unsat341 : Unsatisfiable (PosFin 31) f341 := by
  apply lratCheckerSound f341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p341
  · intro a ha; simp [p341] at ha; subst a; trivial
  · exact checked341
theorem derived341 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c341 := by
  apply localUnsat_implies_entails f341 [c339, c331, c326, c96] c341 unsat341 (by rfl) a
  have h0 : Entails.eval a c339 := derived339 a h
  have h1 : Entails.eval a c331 := derived331 a h
  have h2 : Entails.eval a c326 := derived326 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c342 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f342 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c341, some c340, some c329, some c334, some c335, some c324, some c156]
def p342 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked342 : lratChecker f342 p342 = .success := by decide +kernel
theorem unsat342 : Unsatisfiable (PosFin 31) f342 := by
  apply lratCheckerSound f342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p342
  · intro a ha; simp [p342] at ha; subst a; trivial
  · exact checked342
theorem derived342 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c342 := by
  apply localUnsat_implies_entails f342 [c341, c340, c329, c334, c335, c324, c156] c342 unsat342 (by rfl) a
  have h0 : Entails.eval a c341 := derived341 a h
  have h1 : Entails.eval a c340 := derived340 a h
  have h2 : Entails.eval a c329 := derived329 a h
  have h3 : Entails.eval a c334 := derived334 a h
  have h4 : Entails.eval a c335 := derived335 a h
  have h5 : Entails.eval a c324 := derived324 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived342

end CochromaticTwenty.Certificates.Z12Direct_5_7_7
