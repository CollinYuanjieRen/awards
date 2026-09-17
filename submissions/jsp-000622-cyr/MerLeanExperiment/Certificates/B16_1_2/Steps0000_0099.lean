import MerLeanExperiment.Certificates.B16_1_2.Inputs

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c394 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c266, some c236, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 57) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c264, c266, c236] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c183, some c165, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 57) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c177, c183, c165] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c336, some c341, some c395, some c165, some c147, some c180, some c320, some c299, some c155, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 57) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c336, c341, c395, c165, c147, c180, c320, c299, c155] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c336 := h 335 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c395 := derived395 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c180 := h 179 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c299, some c293, some c281, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 57) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c299, c293, c281] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c299 := h 298 (by decide)
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c380, some c367, some c336, some c341, some c395, some c190, some c396, some c203, some c397, some c155, some c320, some c296, some c281, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 57) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c388, c380, c367, c336, c341, c395, c190, c396, c203, c397, c155, c320, c296, c281] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c336 := h 335 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c395 := derived395 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c396 := derived396 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c397 := derived397 a h
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c320 := h 319 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨34, by decide⟩, true), (⟨39, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c296, some c281, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 57) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c320, c296, c281] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c399, some c148, some c180, some c188, some c165, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 57) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c399, c148, c180, c188, c165] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c399 := derived399 a h
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c148, some c283, some c180, some c188, some c299, some c293, some c153, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 57) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c148, c283, c180, c188, c299, c293, c153] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c148 := h 147 (by decide)
  have h1 : Entails.eval a c283 := h 282 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c299 := h 298 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c400, some c333, some c401, some c320, some c147, some c183, some c188, some c167, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 57) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c400, c333, c401, c320, c147, c183, c188, c167] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c400 := derived400 a h
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c401 := derived401 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c183, some c153, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 57) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c177, c183, c153] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c388, some c380, some c366, some c367, some c398, some c402, some c338, some c401, some c320, some c319, some c296, some c403, some c190, some c167, some c202, some c188, some c160, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 57) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c391, c388, c380, c366, c367, c398, c402, c338, c401, c320, c319, c296, c403, c190, c167, c202, c188, c160] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c398 := derived398 a h
  have h6 : Entails.eval a c402 := derived402 a h
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c401 := derived401 a h
  have h9 : Entails.eval a c320 := h 319 (by decide)
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c403 := derived403 a h
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c188 := h 187 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c153, some c189, some c203, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 57) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c180, c153, c189, c203] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c153 := h 152 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨40, by decide⟩, true), (⟨16, by decide⟩, true), (⟨32, by decide⟩, false), (⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c296, some c320, some c171, some c355, some c353, some c399, some c284, some c333, some c316, some c167, some c152, some c177, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 57) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c296, c320, c171, c355, c353, c399, c284, c333, c316, c167, c152, c177] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c353 := h 352 (by decide)
  have h5 : Entails.eval a c399 := derived399 a h
  have h6 : Entails.eval a c284 := h 283 (by decide)
  have h7 : Entails.eval a c333 := h 332 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c208, some c190, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 57) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c201, c208, c190] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c296, some c320, some c393, some c388, some c367, some c85, some c406, some c407, some c7, some c160, some c153, some c119, some c177, some c205, some c25, some c11, some c167, some c169, some c77, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 57) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c296, c320, c393, c388, c367, c85, c406, c407, c7, c160, c153, c119, c177, c205, c25, c11, c167, c169, c77] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c406 := derived406 a h
  have h7 : Entails.eval a c407 := derived407 a h
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c177 := h 176 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨30, by decide⟩, true), (⟨56, by decide⟩, false), (⟨32, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c408, some c336, some c357, some c399, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 57) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c408, c336, c357, c399] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c408 := derived408 a h
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c399 := derived399 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c410 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨41, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c388, some c320, some c319, some c296, some c405, some c409, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 57) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c391, c388, c320, c319, c296, c405, c409] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  have h5 : Entails.eval a c405 := derived405 a h
  have h6 : Entails.eval a c409 := derived409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c118, some c104, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false))]
def p411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 57) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c119, c118, c104] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c268, some c252, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 57) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c267, c268, c252] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c413 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨24, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c411, some c9, some c85, some c105, some c106, some c122, some c120, some c42, some c104, some c265, some c124, some c40, some c225, some c102, some c300, some c173, some c5, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 57) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c36, c411, c9, c85, c105, c106, c122, c120, c42, c104, c265, c124, c40, c225, c102, c300, c173, c5] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c411 := derived411 a h
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c411, some c9, some c105, some c29, some c122, some c42, some c6, some c126, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 57) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c411, c9, c105, c29, c122, c42, c6, c126] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c411 := derived411 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c106, some c120, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 57) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c105, c106, c120] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c121, some c11, some c87, some c104, some c177, some c117, some c153, some c27, some c407, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 57) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c120, c121, c11, c87, c104, c177, c117, c153, c27, c407] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c177 := h 176 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c407 := derived407 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨47, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c53, some c415, some c416, some c10, some c30, some c61, some c131, some c117, some c160, some c27, some c407, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 57) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c265, c53, c415, c416, c10, c30, c61, c131, c117, c160, c27, c407] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c415 := derived415 a h
  have h3 : Entails.eval a c416 := derived416 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c407 := derived407 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c404, some c391, some c388, some c383, some c412, some c413, some c320, some c319, some c296, some c410, some c405, some c292, some c414, some c417, some c252, some c214, some c266, some c354, some c356, some c239, some c226, some c355, some c316, some c284, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 57) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c393, c404, c391, c388, c383, c412, c413, c320, c319, c296, c410, c405, c292, c414, c417, c252, c214, c266, c354, c356, c239, c226, c355, c316, c284] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c404 := derived404 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c412 := derived412 a h
  have h6 : Entails.eval a c413 := derived413 a h
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c410 := derived410 a h
  have h11 : Entails.eval a c405 := derived405 a h
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c414 := derived414 a h
  have h14 : Entails.eval a c417 := derived417 a h
  have h15 : Entails.eval a c252 := h 251 (by decide)
  have h16 : Entails.eval a c214 := h 213 (by decide)
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c354 := h 353 (by decide)
  have h19 : Entails.eval a c356 := h 355 (by decide)
  have h20 : Entails.eval a c239 := h 238 (by decide)
  have h21 : Entails.eval a c226 := h 225 (by decide)
  have h22 : Entails.eval a c355 := h 354 (by decide)
  have h23 : Entails.eval a c316 := h 315 (by decide)
  have h24 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨46, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c415, some c121, some c120, some c104, some c98, some c11, some c117, some c27, some c102, some c182, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 57) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c415, c121, c120, c104, c98, c11, c117, c27, c102, c182] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c415 := derived415 a h
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, true), (⟨24, by decide⟩, true), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c265, some c250, some c226, some c214, some c316, some c354, some c356, some c279, some c239, some c329, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 57) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c264, c265, c250, c226, c214, c316, c354, c356, c279, c239, c329] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c250 := h 249 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  have h4 : Entails.eval a c214 := h 213 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c279 := h 278 (by decide)
  have h9 : Entails.eval a c239 := h 238 (by decide)
  have h10 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c391, some c388, some c404, some c418, some c86, some c366, some c379, some c412, some c413, some c319, some c292, some c414, some c420, some c53, some c121, some c419, some c6, some c176, some c206, some c189, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 57) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c393, c391, c388, c404, c418, c86, c366, c379, c412, c413, c319, c292, c414, c420, c53, c121, c419, c6, c176, c206, c189] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c404 := derived404 a h
  have h4 : Entails.eval a c418 := derived418 a h
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c412 := derived412 a h
  have h9 : Entails.eval a c413 := derived413 a h
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c414 := derived414 a h
  have h13 : Entails.eval a c420 := derived420 a h
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c419 := derived419 a h
  have h17 : Entails.eval a c6 := h 5 (by decide)
  have h18 : Entails.eval a c176 := h 175 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c413, some c411, some c42, some c319, some c9, some c415, some c265, some c6, some c126, some c47, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 57) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c391, c413, c411, c42, c319, c9, c415, c265, c6, c126, c47] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c413 := derived413 a h
  have h2 : Entails.eval a c411 := derived411 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c415 := derived415 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨24, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c317, some c216, some c225, some c356, some c357, some c264, some c265, some c227, some c238, some c318, some c353, some c284, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 57) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c319, c317, c216, c225, c356, c357, c264, c265, c227, c238, c318, c353, c284] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c6, some c68, some c265, some c119, some c9, some c415, some c126, some c47, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 57) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c34, c6, c68, c265, c119, c9, c415, c126, c47] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c415 := derived415 a h
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c122, some c105, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 57) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c118, c122, c105] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c426 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c421, some c393, some c391, some c388, some c44, some c423, some c425, some c424, some c320, some c318, some c216, some c227, some c356, some c357, some c286, some c394, some c353, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 57) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c421, c393, c391, c388, c44, c423, c425, c424, c320, c318, c216, c227, c356, c357, c286, c394, c353] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c421 := derived421 a h
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c423 := derived423 a h
  have h6 : Entails.eval a c425 := derived425 a h
  have h7 : Entails.eval a c424 := derived424 a h
  have h8 : Entails.eval a c320 := h 319 (by decide)
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c356 := h 355 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  have h15 : Entails.eval a c394 := derived394 a h
  have h16 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c426, some c268, some c267, some c214, some c228, some c354, some c356, some c320, some c318, some c287, some c226, some c355, some c394, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 57) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c426, c268, c267, c214, c228, c354, c356, c320, c318, c287, c226, c355, c394] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c426 := derived426 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c287 := h 286 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c394 := derived394 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨29, by decide⟩, true), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c287, some c353, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 57) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c285, c287, c353] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨24, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c267, some c356, some c357, some c240, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 57) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c268, c267, c356, c357, c240] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c426, some c267, some c268, some c427, some c319, some c317, some c429, some c285, some c428, some c353, some c354, some c318, some c238, some c224, some c264, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 57) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c426, c267, c268, c427, c319, c317, c429, c285, c428, c353, c354, c318, c238, c224, c264] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c426 := derived426 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c427 := derived427 a h
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c429 := derived429 a h
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c428 := derived428 a h
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c354 := h 353 (by decide)
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨20, by decide⟩, false), (⟨36, by decide⟩, false), (⟨29, by decide⟩, false), (⟨24, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c318, some c215, some c355, some c35, some c267, some c430, some c393, some c388, some c238, some c275, some c234, some c79, some c87, some c106, some c31, some c338, some c337, some c119, some c117, some c298, some c412, some c368, some c103, some c379, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 57) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c268, c318, c215, c355, c35, c267, c430, c393, c388, c238, c275, c234, c79, c87, c106, c31, c338, c337, c119, c117, c298, c412, c368, c103, c379] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c430 := derived430 a h
  have h7 : Entails.eval a c393 := h 392 (by decide)
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c238 := h 237 (by decide)
  have h10 : Entails.eval a c275 := h 274 (by decide)
  have h11 : Entails.eval a c234 := h 233 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c31 := h 30 (by decide)
  have h16 : Entails.eval a c338 := h 337 (by decide)
  have h17 : Entails.eval a c337 := h 336 (by decide)
  have h18 : Entails.eval a c119 := h 118 (by decide)
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c298 := h 297 (by decide)
  have h21 : Entails.eval a c412 := derived412 a h
  have h22 : Entails.eval a c368 := h 367 (by decide)
  have h23 : Entails.eval a c103 := h 102 (by decide)
  have h24 : Entails.eval a c379 := h 378 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, true), (⟨38, by decide⟩, false), (⟨36, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c415, some c81, some c71, some c42, some c50, some c340, some c79, some c368, some c230, some c290, some c128, some c141, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 57) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c415, c81, c71, c42, c50, c340, c79, c368, c230, c290, c128, c141] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c415 := derived415 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c340 := h 339 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c368 := h 367 (by decide)
  have h8 : Entails.eval a c230 := h 229 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨32, by decide⟩, true), (⟨52, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c65, some c119, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 57) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c107, c65, c119] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨29, by decide⟩, false), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c268, some c318, some c35, some c215, some c267, some c228, some c148, some c430, some c393, some c391, some c388, some c285, some c224, some c431, some c433, some c415, some c81, some c432, some c117, some c275, some c54, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 57) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c216, c268, c318, c35, c215, c267, c228, c148, c430, c393, c391, c388, c285, c224, c431, c433, c415, c81, c432, c117, c275, c54] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c430 := derived430 a h
  have h9 : Entails.eval a c393 := h 392 (by decide)
  have h10 : Entails.eval a c391 := h 390 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c431 := derived431 a h
  have h15 : Entails.eval a c433 := derived433 a h
  have h16 : Entails.eval a c415 := derived415 a h
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c432 := derived432 a h
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c275 := h 274 (by decide)
  have h21 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c268, some c393, some c388, some c318, some c215, some c35, some c434, some c327, some c283, some c79, some c106, some c63, some c119, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 57) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c216, c268, c393, c388, c318, c215, c35, c434, c327, c283, c79, c106, c63, c119] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c434 := derived434 a h
  have h8 : Entails.eval a c327 := h 326 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c117, some c67, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 57) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c119, c117, c67] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c87, some c63, some c299, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 57) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c87, c63, c299] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c87 := h 86 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨38, by decide⟩, false), (⟨31, by decide⟩, false), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨40, by decide⟩, true), (⟨32, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c287, some c148, some c216, some c436, some c43, some c56, some c425, some c70, some c67, some c437, some c78, some c283, some c299, some c367, some c291, some c141, some c209, some c128, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 57) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c287, c148, c216, c436, c43, c56, c425, c70, c67, c437, c78, c283, c299, c367, c291, c141, c209, c128] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c287 := h 286 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c436 := derived436 a h
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c425 := derived425 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c437 := derived437 a h
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c415, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 57) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c107, c415] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c415 := derived415 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c440 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c388, some c391, some c393, some c430, some c439, some c216, some c287, some c267, some c355, some c438, some c240, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 57) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c318, c388, c391, c393, c430, c439, c216, c287, c267, c355, c438, c240] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c430 := derived430 a h
  have h5 : Entails.eval a c439 := derived439 a h
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c438 := derived438 a h
  have h11 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨23, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c120, some c5, some c10, some c49, some c407, some c131, some c28, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 57) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c123, c120, c5, c10, c49, c407, c131, c28] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c407 := derived407 a h
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c227, some c43, some c441, some c11, some c87, some c299, some c223, some c275, some c134, some c236, some c5, some c80, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 57) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c227, c43, c441, c11, c87, c299, c223, c275, c134, c236, c5, c80] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c227 := h 226 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c441 := derived441 a h
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c134 := h 133 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨7, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c233, some c76, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 57) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c49, c233, c76] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c233 := h 232 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c391, some c393, some c430, some c439, some c318, some c436, some c43, some c404, some c440, some c356, some c357, some c429, some c240, some c44, some c227, some c425, some c443, some c273, some c52, some c441, some c442, some c11, some c87, some c145, some c299, some c134, some c223, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 57) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c388, c391, c393, c430, c439, c318, c436, c43, c404, c440, c356, c357, c429, c240, c44, c227, c425, c443, c273, c52, c441, c442, c11, c87, c145, c299, c134, c223] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c430 := derived430 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c436 := derived436 a h
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c404 := derived404 a h
  have h9 : Entails.eval a c440 := derived440 a h
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c429 := derived429 a h
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  have h16 : Entails.eval a c425 := derived425 a h
  have h17 : Entails.eval a c443 := derived443 a h
  have h18 : Entails.eval a c273 := h 272 (by decide)
  have h19 : Entails.eval a c52 := h 51 (by decide)
  have h20 : Entails.eval a c441 := derived441 a h
  have h21 : Entails.eval a c442 := derived442 a h
  have h22 : Entails.eval a c11 := h 10 (by decide)
  have h23 : Entails.eval a c87 := h 86 (by decide)
  have h24 : Entails.eval a c145 := h 144 (by decide)
  have h25 : Entails.eval a c299 := h 298 (by decide)
  have h26 : Entails.eval a c134 := h 133 (by decide)
  have h27 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c391, some c393, some c430, some c439, some c444, some c215, some c35, some c357, some c436, some c435, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 57) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c388, c391, c393, c430, c439, c444, c215, c35, c357, c436, c435] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c430 := derived430 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c444 := derived444 a h
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c436 := derived436 a h
  have h10 : Entails.eval a c435 := derived435 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨31, by decide⟩, true), (⟨7, by decide⟩, true), (⟨39, by decide⟩, true), (⟨8, by decide⟩, false), (⟨40, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c281, some c61, some c76, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true))]
def p446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 57) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c281, c61, c76] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c281 := h 280 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨4, by decide⟩, false), (⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, false), (⟨23, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c439, some c72, some c76, some c120, some c229, some c11, some c127, some c189, some c191, some c204, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 57) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c439, c72, c76, c120, c229, c11, c127, c189, c191, c204] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨4, by decide⟩, false), (⟨26, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c439, some c447, some c86, some c48, some c295, some c123, some c411, some c11, some c87, some c183, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 57) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c439, c447, c86, c48, c295, c123, c411, c11, c87, c183] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c447 := derived447 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c411 := derived411 a h
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c391, some c393, some c430, some c439, some c445, some c266, some c268, some c216, some c36, some c227, some c356, some c357, some c119, some c318, some c288, some c147, some c446, some c325, some c225, some c284, some c64, some c448, some c273, some c272, some c238, some c234, some c364, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 57) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c388, c391, c393, c430, c439, c445, c266, c268, c216, c36, c227, c356, c357, c119, c318, c288, c147, c446, c325, c225, c284, c64, c448, c273, c272, c238, c234, c364] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c430 := derived430 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c445 := derived445 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c288 := h 287 (by decide)
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c446 := derived446 a h
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c225 := h 224 (by decide)
  have h20 : Entails.eval a c284 := h 283 (by decide)
  have h21 : Entails.eval a c64 := h 63 (by decide)
  have h22 : Entails.eval a c448 := derived448 a h
  have h23 : Entails.eval a c273 := h 272 (by decide)
  have h24 : Entails.eval a c272 := h 271 (by decide)
  have h25 : Entails.eval a c238 := h 237 (by decide)
  have h26 : Entails.eval a c234 := h 233 (by decide)
  have h27 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨7, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c61, some c296, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 57) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c86, c61, c296] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨39, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c215, some c268, some c288, some c147, some c388, some c68, some c425, some c70, some c44, some c450, some c75, some c399, some c366, some c292, some c141, some c209, some c127, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 57) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c320, c215, c268, c288, c147, c388, c68, c425, c70, c44, c450, c75, c399, c366, c292, c141, c209, c127] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c425 := derived425 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c450 := derived450 a h
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c399 := derived399 a h
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c452 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c215, some c266, some c268, some c451, some c119, some c117, some c55, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 57) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c320, c215, c266, c268, c451, c119, c117, c55] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c451 := derived451 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c235, some c51, some c79, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 57) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c235, c51, c79] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c235 := h 234 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨48, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c228, some c121, some c81, some c10, some c86, some c146, some c296, some c131, some c221, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 57) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c228, c121, c81, c10, c86, c146, c296, c131, c221] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c228 := h 227 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨7, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c391, some c393, some c430, some c439, some c117, some c119, some c449, some c319, some c452, some c357, some c355, some c320, some c239, some c44, some c266, some c404, some c453, some c275, some c53, some c248, some c237, some c224, some c454, some c66, some c327, some c300, some c62, some c102, some c79, some c340, some c282, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 57) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c388, c391, c393, c430, c439, c117, c119, c449, c319, c452, c357, c355, c320, c239, c44, c266, c404, c453, c275, c53, c248, c237, c224, c454, c66, c327, c300, c62, c102, c79, c340, c282] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c430 := derived430 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c449 := derived449 a h
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c452 := derived452 a h
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c404 := derived404 a h
  have h17 : Entails.eval a c453 := derived453 a h
  have h18 : Entails.eval a c275 := h 274 (by decide)
  have h19 : Entails.eval a c53 := h 52 (by decide)
  have h20 : Entails.eval a c248 := h 247 (by decide)
  have h21 : Entails.eval a c237 := h 236 (by decide)
  have h22 : Entails.eval a c224 := h 223 (by decide)
  have h23 : Entails.eval a c454 := derived454 a h
  have h24 : Entails.eval a c66 := h 65 (by decide)
  have h25 : Entails.eval a c327 := h 326 (by decide)
  have h26 : Entails.eval a c300 := h 299 (by decide)
  have h27 : Entails.eval a c62 := h 61 (by decide)
  have h28 : Entails.eval a c102 := h 101 (by decide)
  have h29 : Entails.eval a c79 := h 78 (by decide)
  have h30 : Entails.eval a c340 := h 339 (by decide)
  have h31 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨32, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c320, some c267, some c268, some c228, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 57) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c319, c320, c267, c268, c228] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c388, some c393, some c430, some c439, some c449, some c320, some c319, some c452, some c355, some c357, some c456, some c239, some c455, some c266, some c35, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 57) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c391, c388, c393, c430, c439, c449, c320, c319, c452, c355, c357, c456, c239, c455, c266, c35] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c393 := h 392 (by decide)
  have h3 : Entails.eval a c430 := derived430 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c449 := derived449 a h
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c452 := derived452 a h
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c456 := derived456 a h
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c455 := derived455 a h
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨21, by decide⟩, false), (⟨40, by decide⟩, true), (⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c117, some c453, some c13, some c108, some c275, some c134, some c53, some c11, some c120, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 57) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c119, c117, c453, c13, c108, c275, c134, c53, c11, c120] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c453 := derived453 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c275 := h 274 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨21, by decide⟩, false), (⟨40, by decide⟩, true), (⟨22, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, false), (⟨24, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c458, some c9, some c106, some c415, some c439, some c124, some c265, some c13, some c47, some c125, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 57) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c458, c9, c106, c415, c439, c124, c265, c13, c47, c125] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c458 := derived458 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c415 := derived415 a h
  have h4 : Entails.eval a c439 := derived439 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨35, by decide⟩, true), (⟨51, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c354, some c282, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 57) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c313, c354, c282] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨52, by decide⟩, true), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨19, by decide⟩, false), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c105, some c107, some c121, some c120, some c74, some c6, some c62, some c202, some c324, some c167, some c221, some c142, some c129, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 57) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c9, c105, c107, c121, c120, c74, c6, c62, c202, c324, c167, c221, c142, c129] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c142 := h 141 (by decide)
  have h13 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c228, some c35, some c215, some c459, some c352, some c235, some c275, some c237, some c224, some c460, some c461, some c119, some c117, some c71, some c53, some c13, some c108, some c121, some c120, some c134, some c6, some c23, some c162, some c202, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 57) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c228, c35, c215, c459, c352, c235, c275, c237, c224, c460, c461, c119, c117, c71, c53, c13, c108, c121, c120, c134, c6, c23, c162, c202] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c228 := h 227 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c459 := derived459 a h
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c275 := h 274 (by decide)
  have h7 : Entails.eval a c237 := h 236 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  have h9 : Entails.eval a c460 := derived460 a h
  have h10 : Entails.eval a c461 := derived461 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c120 := h 119 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c6 := h 5 (by decide)
  have h21 : Entails.eval a c23 := h 22 (by decide)
  have h22 : Entails.eval a c162 := h 161 (by decide)
  have h23 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c463 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨32, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c456, some c319, some c320, some c457, some c391, some c388, some c215, some c35, some c357, some c462, some c239, some c82, some c13, some c89, some c55, some c119, some c9, some c85, some c173, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked463 : lratChecker f463 p463 = .success := by decide +kernel
theorem unsat463 : Unsatisfiable (PosFin 57) f463 := by
  apply lratCheckerSound f463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p463
  · intro a ha; simp [p463] at ha; subst a; trivial
  · exact checked463
theorem derived463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c463 := by
  apply localUnsat_implies_entails f463 [c456, c319, c320, c457, c391, c388, c215, c35, c357, c462, c239, c82, c13, c89, c55, c119, c9, c85, c173] c463 unsat463 (by rfl) a
  have h0 : Entails.eval a c456 := derived456 a h
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c457 := derived457 a h
  have h4 : Entails.eval a c391 := h 390 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c462 := derived462 a h
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c9 := h 8 (by decide)
  have h17 : Entails.eval a c85 := h 84 (by decide)
  have h18 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c464 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨41, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c89, some c173, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false))]
def p464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked464 : lratChecker f464 p464 = .success := by decide +kernel
theorem unsat464 : Unsatisfiable (PosFin 57) f464 := by
  apply lratCheckerSound f464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p464
  · intro a ha; simp [p464] at ha; subst a; trivial
  · exact checked464
theorem derived464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c464 := by
  apply localUnsat_implies_entails f464 [c13, c89, c173] c464 unsat464 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c465 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c263, some c235, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked465 : lratChecker f465 p465 = .success := by decide +kernel
theorem unsat465 : Unsatisfiable (PosFin 57) f465 := by
  apply lratCheckerSound f465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p465
  · intro a ha; simp [p465] at ha; subst a; trivial
  · exact checked465
theorem derived465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c465 := by
  apply localUnsat_implies_entails f465 [c352, c263, c235] c465 unsat465 (by rfl) a
  have h0 : Entails.eval a c352 := h 351 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c466 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c85, some c464, some c106, some c124, some c68, some c7, some c425, some c127, some c44, some c29, some c292, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked466 : lratChecker f466 p466 = .success := by decide +kernel
theorem unsat466 : Unsatisfiable (PosFin 57) f466 := by
  apply lratCheckerSound f466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p466
  · intro a ha; simp [p466] at ha; subst a; trivial
  · exact checked466
theorem derived466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c466 := by
  apply localUnsat_implies_entails f466 [c9, c85, c464, c106, c124, c68, c7, c425, c127, c44, c29, c292] c466 unsat466 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c464 := derived464 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c425 := derived425 a h
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c467 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c7, some c425, some c407, some c203, some c13, some c171, some c123, some c365, some c53, some c25, some c235, some c167, some c133, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked467 : lratChecker f467 p467 = .success := by decide +kernel
theorem unsat467 : Unsatisfiable (PosFin 57) f467 := by
  apply lratCheckerSound f467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p467
  · intro a ha; simp [p467] at ha; subst a; trivial
  · exact checked467
theorem derived467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c467 := by
  apply localUnsat_implies_entails f467 [c68, c7, c425, c407, c203, c13, c171, c123, c365, c53, c25, c235, c167, c133] c467 unsat467 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c425 := derived425 a h
  have h3 : Entails.eval a c407 := derived407 a h
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c235 := h 234 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c468 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c119, some c458, some c55, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked468 : lratChecker f468 p468 = .success := by decide +kernel
theorem unsat468 : Unsatisfiable (PosFin 57) f468 := by
  apply lratCheckerSound f468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p468
  · intro a ha; simp [p468] at ha; subst a; trivial
  · exact checked468
theorem derived468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c468 := by
  apply localUnsat_implies_entails f468 [c124, c119, c458, c55] c468 unsat468 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c458 := derived458 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c469 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c468, some c68, some c7, some c467, some c425, some c407, some c189, some c190, some c13, some c204, some c135, some c123, some c191, some c4, some c235, some c53, some c265, some c365, some c222, some c145, some c327, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked469 : lratChecker f469 p469 = .success := by decide +kernel
theorem unsat469 : Unsatisfiable (PosFin 57) f469 := by
  apply lratCheckerSound f469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p469
  · intro a ha; simp [p469] at ha; subst a; trivial
  · exact checked469
theorem derived469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c469 := by
  apply localUnsat_implies_entails f469 [c468, c68, c7, c467, c425, c407, c189, c190, c13, c204, c135, c123, c191, c4, c235, c53, c265, c365, c222, c145, c327] c469 unsat469 (by rfl) a
  have h0 : Entails.eval a c468 := derived468 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c467 := derived467 a h
  have h4 : Entails.eval a c425 := derived425 a h
  have h5 : Entails.eval a c407 := derived407 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c191 := h 190 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c265 := h 264 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c222 := h 221 (by decide)
  have h19 : Entails.eval a c145 := h 144 (by decide)
  have h20 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c470 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c366, some c369, some c378, some c384, some c182, some c13, some c117, some c68, some c100, some c121, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked470 : lratChecker f470 p470 = .success := by decide +kernel
theorem unsat470 : Unsatisfiable (PosFin 57) f470 := by
  apply lratCheckerSound f470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p470
  · intro a ha; simp [p470] at ha; subst a; trivial
  · exact checked470
theorem derived470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c470 := by
  apply localUnsat_implies_entails f470 [c86, c366, c369, c378, c384, c182, c13, c117, c68, c100, c121] c470 unsat470 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c369 := h 368 (by decide)
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c471 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, true), (⟨1, by decide⟩, false), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c470, some c177, some c189, some c192, some c201, some c182, some c7, some c89, some c117, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked471 : lratChecker f471 p471 = .success := by decide +kernel
theorem unsat471 : Unsatisfiable (PosFin 57) f471 := by
  apply lratCheckerSound f471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p471
  · intro a ha; simp [p471] at ha; subst a; trivial
  · exact checked471
theorem derived471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c471 := by
  apply localUnsat_implies_entails f471 [c470, c177, c189, c192, c201, c182, c7, c89, c117] c471 unsat471 (by rfl) a
  have h0 : Entails.eval a c470 := derived470 a h
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c472 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c469, some c11, some c87, some c471, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked472 : lratChecker f472 p472 = .success := by decide +kernel
theorem unsat472 : Unsatisfiable (PosFin 57) f472 := by
  apply lratCheckerSound f472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p472
  · intro a ha; simp [p472] at ha; subst a; trivial
  · exact checked472
theorem derived472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c472 := by
  apply localUnsat_implies_entails f472 [c469, c11, c87, c471] c472 unsat472 (by rfl) a
  have h0 : Entails.eval a c469 := derived469 a h
  have h1 : Entails.eval a c11 := h 10 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c471 := derived471 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c473 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c465, some c466, some c472, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked473 : lratChecker f473 p473 = .success := by decide +kernel
theorem unsat473 : Unsatisfiable (PosFin 57) f473 := by
  apply lratCheckerSound f473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p473
  · intro a ha; simp [p473] at ha; subst a; trivial
  · exact checked473
theorem derived473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c473 := by
  apply localUnsat_implies_entails f473 [c465, c466, c472] c473 unsat473 (by rfl) a
  have h0 : Entails.eval a c465 := derived465 a h
  have h1 : Entails.eval a c466 := derived466 a h
  have h2 : Entails.eval a c472 := derived472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c474 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨39, by decide⟩, true), (⟨32, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c147, some c463, some c456, some c319, some c457, some c391, some c451, some c119, some c117, some c13, some c55, some c138, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked474 : lratChecker f474 p474 = .success := by decide +kernel
theorem unsat474 : Unsatisfiable (PosFin 57) f474 := by
  apply lratCheckerSound f474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p474
  · intro a ha; simp [p474] at ha; subst a; trivial
  · exact checked474
theorem derived474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c474 := by
  apply localUnsat_implies_entails f474 [c320, c147, c463, c456, c319, c457, c391, c451, c119, c117, c13, c55, c138] c474 unsat474 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c456 := derived456 a h
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c457 := derived457 a h
  have h6 : Entails.eval a c391 := h 390 (by decide)
  have h7 : Entails.eval a c451 := derived451 a h
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c475 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨32, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c463, some c456, some c319, some c320, some c457, some c391, some c388, some c473, some c147, some c474, some c9, some c85, some c466, some c201, some c203, some c127, some c464, some c263, some c171, some c235, some c46, some c78, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked475 : lratChecker f475 p475 = .success := by decide +kernel
theorem unsat475 : Unsatisfiable (PosFin 57) f475 := by
  apply lratCheckerSound f475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p475
  · intro a ha; simp [p475] at ha; subst a; trivial
  · exact checked475
theorem derived475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c475 := by
  apply localUnsat_implies_entails f475 [c463, c456, c319, c320, c457, c391, c388, c473, c147, c474, c9, c85, c466, c201, c203, c127, c464, c263, c171, c235, c46, c78] c475 unsat475 (by rfl) a
  have h0 : Entails.eval a c463 := derived463 a h
  have h1 : Entails.eval a c456 := derived456 a h
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c457 := derived457 a h
  have h5 : Entails.eval a c391 := h 390 (by decide)
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c473 := derived473 a h
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c474 := derived474 a h
  have h10 : Entails.eval a c9 := h 8 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c466 := derived466 a h
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c464 := derived464 a h
  have h17 : Entails.eval a c263 := h 262 (by decide)
  have h18 : Entails.eval a c171 := h 170 (by decide)
  have h19 : Entails.eval a c235 := h 234 (by decide)
  have h20 : Entails.eval a c46 := h 45 (by decide)
  have h21 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c476 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c319, some c475, some c356, some c357, some c288, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked476 : lratChecker f476 p476 = .success := by decide +kernel
theorem unsat476 : Unsatisfiable (PosFin 57) f476 := by
  apply lratCheckerSound f476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p476
  · intro a ha; simp [p476] at ha; subst a; trivial
  · exact checked476
theorem derived476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c476 := by
  apply localUnsat_implies_entails f476 [c320, c319, c475, c356, c357, c288] c476 unsat476 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c475 := derived475 a h
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c477 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c476, some c215, some c288, some c268, some c356, some c216, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked477 : lratChecker f477 p477 = .success := by decide +kernel
theorem unsat477 : Unsatisfiable (PosFin 57) f477 := by
  apply lratCheckerSound f477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p477
  · intro a ha; simp [p477] at ha; subst a; trivial
  · exact checked477
theorem derived477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c477 := by
  apply localUnsat_implies_entails f477 [c476, c215, c288, c268, c356, c216] c477 unsat477 (by rfl) a
  have h0 : Entails.eval a c476 := derived476 a h
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c288 := h 287 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c478 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨31, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c476, some c477, some c357, some c216, some c267, some c268, some c228, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked478 : lratChecker f478 p478 = .success := by decide +kernel
theorem unsat478 : Unsatisfiable (PosFin 57) f478 := by
  apply lratCheckerSound f478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p478
  · intro a ha; simp [p478] at ha; subst a; trivial
  · exact checked478
theorem derived478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c478 := by
  apply localUnsat_implies_entails f478 [c476, c477, c357, c216, c267, c268, c228] c478 unsat478 (by rfl) a
  have h0 : Entails.eval a c476 := derived476 a h
  have h1 : Entails.eval a c477 := derived477 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c479 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c148, some c216, some c9, some c85, some c105, some c128, some c464, some c29, some c124, some c82, some c290, some c106, some c287, some c42, some c352, some c425, some c121, some c283, some c65, some c327, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked479 : lratChecker f479 p479 = .success := by decide +kernel
theorem unsat479 : Unsatisfiable (PosFin 57) f479 := by
  apply lratCheckerSound f479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p479
  · intro a ha; simp [p479] at ha; subst a; trivial
  · exact checked479
theorem derived479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c479 := by
  apply localUnsat_implies_entails f479 [c148, c216, c9, c85, c105, c128, c464, c29, c124, c82, c290, c106, c287, c42, c352, c425, c121, c283, c65, c327] c479 unsat479 (by rfl) a
  have h0 : Entails.eval a c148 := h 147 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c464 := derived464 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c287 := h 286 (by decide)
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c352 := h 351 (by decide)
  have h15 : Entails.eval a c425 := derived425 a h
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c65 := h 64 (by decide)
  have h19 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c480 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c224, some c65, some c121, some c120, some c54, some c50, some c275, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked480 : lratChecker f480 p480 = .success := by decide +kernel
theorem unsat480 : Unsatisfiable (PosFin 57) f480 := by
  apply lratCheckerSound f480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p480
  · intro a ha; simp [p480] at ha; subst a; trivial
  · exact checked480
theorem derived480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c480 := by
  apply localUnsat_implies_entails f480 [c224, c65, c121, c120, c54, c50, c275] c480 unsat480 (by rfl) a
  have h0 : Entails.eval a c224 := h 223 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c481 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨31, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c478, some c476, some c457, some c391, some c388, some c357, some c216, some c267, some c268, some c35, some c479, some c436, some c119, some c117, some c89, some c108, some c480, some c317, some c327, some c300, some c88, some c63, some c120, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 57) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c478, c476, c457, c391, c388, c357, c216, c267, c268, c35, c479, c436, c119, c117, c89, c108, c480, c317, c327, c300, c88, c63, c120] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c478 := derived478 a h
  have h1 : Entails.eval a c476 := derived476 a h
  have h2 : Entails.eval a c457 := derived457 a h
  have h3 : Entails.eval a c391 := h 390 (by decide)
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c479 := derived479 a h
  have h11 : Entails.eval a c436 := derived436 a h
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c108 := h 107 (by decide)
  have h16 : Entails.eval a c480 := derived480 a h
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c327 := h 326 (by decide)
  have h19 : Entails.eval a c300 := h 299 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c63 := h 62 (by decide)
  have h22 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨30, by decide⟩, false), (⟨31, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c215, some c119, some c72, some c446, some c295, some c366, some c290, some c141, some c209, some c127, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 57) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c147, c215, c119, c72, c446, c295, c366, c290, c141, c209, c127] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c446 := derived446 a h
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c483 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨30, by decide⟩, false), (⟨31, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c215, some c482, some c9, some c85, some c127, some c290, some c29, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 57) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c147, c215, c482, c9, c85, c127, c290, c29] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c215 := h 214 (by decide)
  have h2 : Entails.eval a c482 := derived482 a h
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨46, by decide⟩, true), (⟨6, by decide⟩, true), (⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c85, some c127, some c464, some c175, some c104, some c124, some c106, some c46, some c263, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 57) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c9, c85, c127, c464, c175, c104, c124, c106, c46, c263] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c464 := derived464 a h
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c485 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨52, by decide⟩, true), (⟨28, by decide⟩, true), (⟨47, by decide⟩, false), (⟨15, by decide⟩, false), (⟨32, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f485 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c201, some c175, some c157, some c192, some c366, some c368, some c178, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p485 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked485 : lratChecker f485 p485 = .success := by decide +kernel
theorem unsat485 : Unsatisfiable (PosFin 57) f485 := by
  apply lratCheckerSound f485 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p485
  · intro a ha; simp [p485] at ha; subst a; trivial
  · exact checked485
theorem derived485 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c485 := by
  apply localUnsat_implies_entails f485 [c203, c201, c175, c157, c192, c366, c368, c178] c485 unsat485 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c175 := h 174 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c366 := h 365 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c486 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f486 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c476, some c457, some c391, some c388, some c478, some c481, some c215, some c147, some c268, some c216, some c36, some c356, some c425, some c483, some c42, some c484, some c119, some c411, some c446, some c325, some c225, some c284, some c64, some c265, some c485, some c189, some c191, some c137, some c204, some c22, some c166, some c77, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p486 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked486 : lratChecker f486 p486 = .success := by decide +kernel
theorem unsat486 : Unsatisfiable (PosFin 57) f486 := by
  apply lratCheckerSound f486 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p486
  · intro a ha; simp [p486] at ha; subst a; trivial
  · exact checked486
theorem derived486 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c486 := by
  apply localUnsat_implies_entails f486 [c476, c457, c391, c388, c478, c481, c215, c147, c268, c216, c36, c356, c425, c483, c42, c484, c119, c411, c446, c325, c225, c284, c64, c265, c485, c189, c191, c137, c204, c22, c166, c77] c486 unsat486 (by rfl) a
  have h0 : Entails.eval a c476 := derived476 a h
  have h1 : Entails.eval a c457 := derived457 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c478 := derived478 a h
  have h5 : Entails.eval a c481 := derived481 a h
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c425 := derived425 a h
  have h13 : Entails.eval a c483 := derived483 a h
  have h14 : Entails.eval a c42 := h 41 (by decide)
  have h15 : Entails.eval a c484 := derived484 a h
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c411 := derived411 a h
  have h18 : Entails.eval a c446 := derived446 a h
  have h19 : Entails.eval a c325 := h 324 (by decide)
  have h20 : Entails.eval a c225 := h 224 (by decide)
  have h21 : Entails.eval a c284 := h 283 (by decide)
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c265 := h 264 (by decide)
  have h24 : Entails.eval a c485 := derived485 a h
  have h25 : Entails.eval a c189 := h 188 (by decide)
  have h26 : Entails.eval a c191 := h 190 (by decide)
  have h27 : Entails.eval a c137 := h 136 (by decide)
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c22 := h 21 (by decide)
  have h30 : Entails.eval a c166 := h 165 (by decide)
  have h31 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c487 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f487 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c368, some c178, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p487 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked487 : lratChecker f487 p487 = .success := by decide +kernel
theorem unsat487 : Unsatisfiable (PosFin 57) f487 := by
  apply lratCheckerSound f487 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p487
  · intro a ha; simp [p487] at ha; subst a; trivial
  · exact checked487
theorem derived487 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c487 := by
  apply localUnsat_implies_entails f487 [c191, c368, c178] c487 unsat487 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c488 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨9, by decide⟩, true), (⟨30, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f488 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c189, some c425, some c42, some c411, some c267, some c216, some c72, some c141, some c291, some c366, some c487, some c317, some c265, some c225, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p488 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked488 : lratChecker f488 p488 = .success := by decide +kernel
theorem unsat488 : Unsatisfiable (PosFin 57) f488 := by
  apply lratCheckerSound f488 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p488
  · intro a ha; simp [p488] at ha; subst a; trivial
  · exact checked488
theorem derived488 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c488 := by
  apply localUnsat_implies_entails f488 [c391, c189, c425, c42, c411, c267, c216, c72, c141, c291, c366, c487, c317, c265, c225] c488 unsat488 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c425 := derived425 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c411 := derived411 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c366 := h 365 (by decide)
  have h11 : Entails.eval a c487 := derived487 a h
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c489 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f489 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c189, some c267, some c216, some c72, some c141, some c291, some c366, some c382, some c383, some c487, some c249, some c265, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p489 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked489 : lratChecker f489 p489 = .success := by decide +kernel
theorem unsat489 : Unsatisfiable (PosFin 57) f489 := by
  apply lratCheckerSound f489 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p489
  · intro a ha; simp [p489] at ha; subst a; trivial
  · exact checked489
theorem derived489 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c489 := by
  apply localUnsat_implies_entails f489 [c391, c189, c267, c216, c72, c141, c291, c366, c382, c383, c487, c249, c265] c489 unsat489 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c383 := h 382 (by decide)
  have h10 : Entails.eval a c487 := derived487 a h
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c490 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨46, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f490 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c388, some c391, some c425, some c486, some c476, some c489, some c56, some c268, some c216, some c72, some c141, some c291, some c321, some c227, some c269, some c276, some c242, some c223, some c299, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p490 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked490 : lratChecker f490 p490 = .success := by decide +kernel
theorem unsat490 : Unsatisfiable (PosFin 57) f490 := by
  apply lratCheckerSound f490 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p490
  · intro a ha; simp [p490] at ha; subst a; trivial
  · exact checked490
theorem derived490 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c490 := by
  apply localUnsat_implies_entails f490 [c119, c388, c391, c425, c486, c476, c489, c56, c268, c216, c72, c141, c291, c321, c227, c269, c276, c242, c223, c299] c490 unsat490 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c486 := derived486 a h
  have h5 : Entails.eval a c476 := derived476 a h
  have h6 : Entails.eval a c489 := derived489 a h
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c227 := h 226 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c276 := h 275 (by decide)
  have h17 : Entails.eval a c242 := h 241 (by decide)
  have h18 : Entails.eval a c223 := h 222 (by decide)
  have h19 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c491 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨30, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f491 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c486, some c476, some c391, some c388, some c189, some c488, some c490, some c43, some c268, some c216, some c72, some c141, some c321, some c290, some c227, some c366, some c269, some c276, some c242, some c223, some c177, some c315, some c190, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p491 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked491 : lratChecker f491 p491 = .success := by decide +kernel
theorem unsat491 : Unsatisfiable (PosFin 57) f491 := by
  apply lratCheckerSound f491 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p491
  · intro a ha; simp [p491] at ha; subst a; trivial
  · exact checked491
theorem derived491 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c491 := by
  apply localUnsat_implies_entails f491 [c119, c486, c476, c391, c388, c189, c488, c490, c43, c268, c216, c72, c141, c321, c290, c227, c366, c269, c276, c242, c223, c177, c315, c190] c491 unsat491 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c486 := derived486 a h
  have h2 : Entails.eval a c476 := derived476 a h
  have h3 : Entails.eval a c391 := h 390 (by decide)
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c488 := derived488 a h
  have h7 : Entails.eval a c490 := derived490 a h
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  have h16 : Entails.eval a c366 := h 365 (by decide)
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c276 := h 275 (by decide)
  have h19 : Entails.eval a c242 := h 241 (by decide)
  have h20 : Entails.eval a c223 := h 222 (by decide)
  have h21 : Entails.eval a c177 := h 176 (by decide)
  have h22 : Entails.eval a c315 := h 314 (by decide)
  have h23 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c492 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f492 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c123, some c108, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p492 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked492 : lratChecker f492 p492 = .success := by decide +kernel
theorem unsat492 : Unsatisfiable (PosFin 57) f492 := by
  apply lratCheckerSound f492 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p492
  · intro a ha; simp [p492] at ha; subst a; trivial
  · exact checked492
theorem derived492 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c492 := by
  apply localUnsat_implies_entails f492 [c120, c123, c108] c492 unsat492 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c493 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨46, by decide⟩, false), (⟨47, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f493 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c425, some c366, some c295, some c382, some c383, some c368, some c100, some c249, some c265, some c492, some c50, some c272, some c210, some c30, some c76, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p493 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked493 : lratChecker f493 p493 = .success := by decide +kernel
theorem unsat493 : Unsatisfiable (PosFin 57) f493 := by
  apply lratCheckerSound f493 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p493
  · intro a ha; simp [p493] at ha; subst a; trivial
  · exact checked493
theorem derived493 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c493 := by
  apply localUnsat_implies_entails f493 [c425, c366, c295, c382, c383, c368, c100, c249, c265, c492, c50, c272, c210, c30, c76] c493 unsat493 (by rfl) a
  have h0 : Entails.eval a c425 := derived425 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c295 := h 294 (by decide)
  have h3 : Entails.eval a c382 := h 381 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c492 := derived492 a h
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived493

end CochromaticTwenty.Certificates.B16_1_2
