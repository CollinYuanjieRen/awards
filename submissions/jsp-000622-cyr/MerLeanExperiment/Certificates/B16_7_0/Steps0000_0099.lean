import MerLeanExperiment.Certificates.B16_7_0.Inputs

/-! Generated from the actual pinned b16_7_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c385 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c362, some c340, some c342, some c324, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked385 : lratChecker f385 p385 = .success := by decide +kernel
theorem unsat385 : Unsatisfiable (PosFin 57) f385 := by
  apply lratCheckerSound f385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p385
  · intro a ha; simp [p385] at ha; subst a; trivial
  · exact checked385
theorem derived385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c385 := by
  apply localUnsat_implies_entails f385 [c364, c362, c340, c342, c324] c385 unsat385 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c362 := h 361 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c342 := h 341 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c386 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c364, some c362, some c208, some c324, some c248, some c249, some c339, some c221, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked386 : lratChecker f386 p386 = .success := by decide +kernel
theorem unsat386 : Unsatisfiable (PosFin 57) f386 := by
  apply lratCheckerSound f386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p386
  · intro a ha; simp [p386] at ha; subst a; trivial
  · exact checked386
theorem derived386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c386 := by
  apply localUnsat_implies_entails f386 [c385, c364, c362, c208, c324, c248, c249, c339, c221] c386 unsat386 (by rfl) a
  have h0 : Entails.eval a c385 := derived385 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c249 := h 248 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c387 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c246, some c248, some c231, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked387 : lratChecker f387 p387 = .success := by decide +kernel
theorem unsat387 : Unsatisfiable (PosFin 57) f387 := by
  apply lratCheckerSound f387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p387
  · intro a ha; simp [p387] at ha; subst a; trivial
  · exact checked387
theorem derived387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c387 := by
  apply localUnsat_implies_entails f387 [c246, c248, c231] c387 unsat387 (by rfl) a
  have h0 : Entails.eval a c246 := h 245 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c388 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c362, some c364, some c385, some c386, some c341, some c387, some c221, some c247, some c249, some c231, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked388 : lratChecker f388 p388 = .success := by decide +kernel
theorem unsat388 : Unsatisfiable (PosFin 57) f388 := by
  apply lratCheckerSound f388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p388
  · intro a ha; simp [p388] at ha; subst a; trivial
  · exact checked388
theorem derived388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c388 := by
  apply localUnsat_implies_entails f388 [c362, c364, c385, c386, c341, c387, c221, c247, c249, c231] c388 unsat388 (by rfl) a
  have h0 : Entails.eval a c362 := h 361 (by decide)
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c385 := derived385 a h
  have h3 : Entails.eval a c386 := derived386 a h
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c387 := derived387 a h
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c247 := h 246 (by decide)
  have h8 : Entails.eval a c249 := h 248 (by decide)
  have h9 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c389 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c247, some c249, some c231, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked389 : lratChecker f389 p389 = .success := by decide +kernel
theorem unsat389 : Unsatisfiable (PosFin 57) f389 := by
  apply lratCheckerSound f389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p389
  · intro a ha; simp [p389] at ha; subst a; trivial
  · exact checked389
theorem derived389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c389 := by
  apply localUnsat_implies_entails f389 [c247, c249, c231] c389 unsat389 (by rfl) a
  have h0 : Entails.eval a c247 := h 246 (by decide)
  have h1 : Entails.eval a c249 := h 248 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c390 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c210, some c340, some c342, some c324, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked390 : lratChecker f390 p390 = .success := by decide +kernel
theorem unsat390 : Unsatisfiable (PosFin 57) f390 := by
  apply lratCheckerSound f390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p390
  · intro a ha; simp [p390] at ha; subst a; trivial
  · exact checked390
theorem derived390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c390 := by
  apply localUnsat_implies_entails f390 [c389, c210, c340, c342, c324] c390 unsat390 (by rfl) a
  have h0 : Entails.eval a c389 := derived389 a h
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c342 := h 341 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c391 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c248, some c249, some c232, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked391 : lratChecker f391 p391 = .success := by decide +kernel
theorem unsat391 : Unsatisfiable (PosFin 57) f391 := by
  apply lratCheckerSound f391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p391
  · intro a ha; simp [p391] at ha; subst a; trivial
  · exact checked391
theorem derived391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c391 := by
  apply localUnsat_implies_entails f391 [c248, c249, c232] c391 unsat391 (by rfl) a
  have h0 : Entails.eval a c248 := h 247 (by decide)
  have h1 : Entails.eval a c249 := h 248 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c392 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c390, some c361, some c391, some c208, some c341, some c342, some c325, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked392 : lratChecker f392 p392 = .success := by decide +kernel
theorem unsat392 : Unsatisfiable (PosFin 57) f392 := by
  apply lratCheckerSound f392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p392
  · intro a ha; simp [p392] at ha; subst a; trivial
  · exact checked392
theorem derived392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c392 := by
  apply localUnsat_implies_entails f392 [c388, c390, c361, c391, c208, c341, c342, c325] c392 unsat392 (by rfl) a
  have h0 : Entails.eval a c388 := derived388 a h
  have h1 : Entails.eval a c390 := derived390 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c391 := derived391 a h
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c341 := h 340 (by decide)
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c393 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c392, some c363, some c388, some c341, some c342, some c325, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked393 : lratChecker f393 p393 = .success := by decide +kernel
theorem unsat393 : Unsatisfiable (PosFin 57) f393 := by
  apply lratCheckerSound f393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p393
  · intro a ha; simp [p393] at ha; subst a; trivial
  · exact checked393
theorem derived393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c393 := by
  apply localUnsat_implies_entails f393 [c392, c363, c388, c341, c342, c325] c393 unsat393 (by rfl) a
  have h0 : Entails.eval a c392 := derived392 a h
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c388 := derived388 a h
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c394 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨38, by decide⟩, true), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c325, some c247, some c339, some c220, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 57) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c210, c325, c247, c339, c220] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c247 := h 246 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  have h4 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨22, by decide⟩, true), (⟨56, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c394, some c340, some c220, some c246, some c247, some c232, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 57) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c394, c340, c220, c246, c247, c232] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c394 := derived394 a h
  have h1 : Entails.eval a c340 := h 339 (by decide)
  have h2 : Entails.eval a c220 := h 219 (by decide)
  have h3 : Entails.eval a c246 := h 245 (by decide)
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c392, some c363, some c391, some c393, some c395, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 57) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c388, c392, c363, c391, c393, c395] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c388 := derived388 a h
  have h1 : Entails.eval a c392 := derived392 a h
  have h2 : Entails.eval a c363 := h 362 (by decide)
  have h3 : Entails.eval a c391 := derived391 a h
  have h4 : Entails.eval a c393 := derived393 a h
  have h5 : Entails.eval a c395 := derived395 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨45, by decide⟩, false), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c175, some c176, some c165, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 57) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c175, c176, c165] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c175 := h 174 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨52, by decide⟩, true), (⟨44, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c397, some c184, some c190, some c171, some c122, some c165, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 57) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c397, c184, c190, c171, c122, c165] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c397 := derived397 a h
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c190 := h 189 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨36, by decide⟩, false), (⟨21, by decide⟩, false), (⟨37, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c232, some c259, some c230, some c338, some c346, some c398, some c56, some c315, some c30, some c366, some c367, some c73, some c80, some c76, some c94, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 57) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c232, c259, c230, c338, c346, c398, c56, c315, c30, c366, c367, c73, c80, c76, c94] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c398 := derived398 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c232, some c111, some c208, some c220, some c259, some c218, some c399, some c58, some c30, some c81, some c68, some c93, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 57) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c232, c111, c208, c220, c259, c218, c399, c58, c30, c81, c68, c93] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c220 := h 219 (by decide)
  have h4 : Entails.eval a c259 := h 258 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c399 := derived399 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨42, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨46, by decide⟩, false), (⟨22, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c230, some c366, some c371, some c223, some c21, some c250, some c34, some c81, some c52, some c262, some c30, some c199, some c196, some c227, some c286, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 57) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c230, c366, c371, c223, c21, c250, c34, c81, c52, c262, c30, c199, c196, c227, c286] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c230 := h 229 (by decide)
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c250 := h 249 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c30 := h 29 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c227 := h 226 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨42, by decide⟩, false), (⟨39, by decide⟩, true), (⟨18, by decide⟩, false), (⟨37, by decide⟩, false), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c232, some c401, some c245, some c253, some c29, some c223, some c37, some c367, some c157, some c271, some c321, some c125, some c106, some c299, some c261, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 57) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c58, c232, c401, c245, c253, c29, c223, c37, c367, c157, c271, c321, c125, c106, c299, c261] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c401 := derived401 a h
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  have h11 : Entails.eval a c321 := h 320 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c299 := h 298 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c213, some c400, some c232, some c111, some c208, some c58, some c318, some c402, some c218, some c253, some c29, some c223, some c55, some c366, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 57) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c213, c400, c232, c111, c208, c58, c318, c402, c218, c253, c29, c223, c55, c366] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c213 := h 212 (by decide)
  have h1 : Entails.eval a c400 := derived400 a h
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c402 := derived402 a h
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨40, by decide⟩, false), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c208, some c232, some c400, some c350, some c403, some c352, some c218, some c245, some c253, some c223, some c157, some c125, some c171, some c106, some c115, some c264, some c189, some c190, some c127, some c175, some c305, some c191, some c135, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 57) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c111, c208, c232, c400, c350, c403, c352, c218, c245, c253, c223, c157, c125, c171, c106, c115, c264, c189, c190, c127, c175, c305, c191, c135] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  have h3 : Entails.eval a c400 := derived400 a h
  have h4 : Entails.eval a c350 := h 349 (by decide)
  have h5 : Entails.eval a c403 := derived403 a h
  have h6 : Entails.eval a c352 := h 351 (by decide)
  have h7 : Entails.eval a c218 := h 217 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c223 := h 222 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c264 := h 263 (by decide)
  have h17 : Entails.eval a c189 := h 188 (by decide)
  have h18 : Entails.eval a c190 := h 189 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c175 := h 174 (by decide)
  have h21 : Entails.eval a c305 := h 304 (by decide)
  have h22 : Entails.eval a c191 := h 190 (by decide)
  have h23 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨34, by decide⟩, true), (⟨20, by decide⟩, false), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c66, some c23, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 57) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c62, c66, c23] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c184, some c10, some c205, some c125, some c106, some c36, some c261, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 57) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c163, c184, c10, c205, c125, c106, c36, c261] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨36, by decide⟩, true), (⟨24, by decide⟩, false), (⟨40, by decide⟩, false), (⟨22, by decide⟩, true), (⟨38, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c218, some c111, some c208, some c396, some c383, some c379, some c245, some c253, some c259, some c220, some c350, some c213, some c241, some c255, some c405, some c406, some c127, some c175, some c176, some c188, some c126, some c305, some c34, some c125, some c4, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 57) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c218, c111, c208, c396, c383, c379, c245, c253, c259, c220, c350, c213, c241, c255, c405, c406, c127, c175, c176, c188, c126, c305, c34, c125, c4] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c396 := derived396 a h
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c253 := h 252 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  have h9 : Entails.eval a c220 := h 219 (by decide)
  have h10 : Entails.eval a c350 := h 349 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c255 := h 254 (by decide)
  have h14 : Entails.eval a c405 := derived405 a h
  have h15 : Entails.eval a c406 := derived406 a h
  have h16 : Entails.eval a c127 := h 126 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c176 := h 175 (by decide)
  have h19 : Entails.eval a c188 := h 187 (by decide)
  have h20 : Entails.eval a c126 := h 125 (by decide)
  have h21 : Entails.eval a c305 := h 304 (by decide)
  have h22 : Entails.eval a c34 := h 33 (by decide)
  have h23 : Entails.eval a c125 := h 124 (by decide)
  have h24 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨23, by decide⟩, true), (⟨36, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c218, some c111, some c208, some c213, some c255, some c251, some c405, some c228, some c406, some c367, some c127, some c108, some c120, some c203, some c186, some c261, some c125, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 57) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c218, c111, c208, c213, c255, c251, c405, c228, c406, c367, c127, c108, c120, c203, c186, c261, c125] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c218 := h 217 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c405 := derived405 a h
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c406 := derived406 a h
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c261 := h 260 (by decide)
  have h16 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨35, by decide⟩, true), (⟨23, by decide⟩, true), (⟨36, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c176, some c147, some c188, some c191, some c117, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 57) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c176, c147, c188, c191, c117] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c176 := h 175 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c410 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨24, by decide⟩, false), (⟨40, by decide⟩, false), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c208, some c396, some c383, some c379, some c218, some c407, some c408, some c348, some c350, some c220, some c256, some c225, some c409, some c163, some c319, some c320, some c371, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 57) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c111, c208, c396, c383, c379, c218, c407, c408, c348, c350, c220, c256, c225, c409, c163, c319, c320, c371] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c407 := derived407 a h
  have h7 : Entails.eval a c408 := derived408 a h
  have h8 : Entails.eval a c348 := h 347 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c256 := h 255 (by decide)
  have h12 : Entails.eval a c225 := h 224 (by decide)
  have h13 : Entails.eval a c409 := derived409 a h
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨35, by decide⟩, true), (⟨21, by decide⟩, false), (⟨37, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c259, some c225, some c163, some c228, some c54, some c320, some c10, some c27, some c371, some c68, some c78, some c28, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 57) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c257, c259, c225, c163, c228, c54, c320, c10, c27, c371, c68, c78, c28] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨50, by decide⟩, true), (⟨34, by decide⟩, false), (⟨52, by decide⟩, true), (⟨36, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c127, some c176, some c175, some c188, some c126, some c266, some c305, some c37, some c34, some c125, some c3, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 57) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c127, c176, c175, c188, c126, c266, c305, c37, c34, c125, c3] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c127 := h 126 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c175 := h 174 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c413 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c379, some c383, some c396, some c404, some c410, some c111, some c208, some c352, some c338, some c346, some c220, some c257, some c213, some c334, some c348, some c412, some c163, some c184, some c205, some c54, some c125, some c106, some c10, some c27, some c18, some c68, some c80, some c52, some c98, some c280, some c37, some c194, some c266, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 57) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c391, c379, c383, c396, c404, c410, c111, c208, c352, c338, c346, c220, c257, c213, c334, c348, c412, c163, c184, c205, c54, c125, c106, c10, c27, c18, c68, c80, c52, c98, c280, c37, c194, c266] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c391 := derived391 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c396 := derived396 a h
  have h4 : Entails.eval a c404 := derived404 a h
  have h5 : Entails.eval a c410 := derived410 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c338 := h 337 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c220 := h 219 (by decide)
  have h12 : Entails.eval a c257 := h 256 (by decide)
  have h13 : Entails.eval a c213 := h 212 (by decide)
  have h14 : Entails.eval a c334 := h 333 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c412 := derived412 a h
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c54 := h 53 (by decide)
  have h21 : Entails.eval a c125 := h 124 (by decide)
  have h22 : Entails.eval a c106 := h 105 (by decide)
  have h23 : Entails.eval a c10 := h 9 (by decide)
  have h24 : Entails.eval a c27 := h 26 (by decide)
  have h25 : Entails.eval a c18 := h 17 (by decide)
  have h26 : Entails.eval a c68 := h 67 (by decide)
  have h27 : Entails.eval a c80 := h 79 (by decide)
  have h28 : Entails.eval a c52 := h 51 (by decide)
  have h29 : Entails.eval a c98 := h 97 (by decide)
  have h30 : Entails.eval a c280 := h 279 (by decide)
  have h31 : Entails.eval a c37 := h 36 (by decide)
  have h32 : Entails.eval a c194 := h 193 (by decide)
  have h33 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨39, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨22, by decide⟩, true), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c209, some c58, some c111, some c208, some c348, some c349, some c344, some c321, some c220, some c367, some c163, some c30, some c203, some c52, some c108, some c86, some c18, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 57) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c209, c58, c111, c208, c348, c349, c344, c321, c220, c367, c163, c30, c203, c52, c108, c86, c18] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c209 := h 208 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c220 := h 219 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c86 := h 85 (by decide)
  have h16 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨42, by decide⟩, false), (⟨18, by decide⟩, false), (⟨34, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c93, some c21, some c92, some c62, some c25, some c78, some c366, some c371, some c222, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 57) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c257, c93, c21, c92, c62, c25, c78, c366, c371, c222] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c127, some c176, some c305, some c126, some c35, some c8, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 57) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c127, c176, c305, c126, c35, c8] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c127 := h 126 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c111, some c208, some c396, some c383, some c379, some c404, some c410, some c413, some c58, some c209, some c414, some c213, some c318, some c241, some c255, some c257, some c415, some c34, some c81, some c416, some c163, some c184, some c227, some c171, some c161, some c13, some c146, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 57) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c391, c111, c208, c396, c383, c379, c404, c410, c413, c58, c209, c414, c213, c318, c241, c255, c257, c415, c34, c81, c416, c163, c184, c227, c171, c161, c13, c146] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c391 := derived391 a h
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c396 := derived396 a h
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c404 := derived404 a h
  have h7 : Entails.eval a c410 := derived410 a h
  have h8 : Entails.eval a c413 := derived413 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c414 := derived414 a h
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c318 := h 317 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c255 := h 254 (by decide)
  have h16 : Entails.eval a c257 := h 256 (by decide)
  have h17 : Entails.eval a c415 := derived415 a h
  have h18 : Entails.eval a c34 := h 33 (by decide)
  have h19 : Entails.eval a c81 := h 80 (by decide)
  have h20 : Entails.eval a c416 := derived416 a h
  have h21 : Entails.eval a c163 := h 162 (by decide)
  have h22 : Entails.eval a c184 := h 183 (by decide)
  have h23 : Entails.eval a c227 := h 226 (by decide)
  have h24 : Entails.eval a c171 := h 170 (by decide)
  have h25 : Entails.eval a c161 := h 160 (by decide)
  have h26 : Entails.eval a c13 := h 12 (by decide)
  have h27 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨25, by decide⟩, false), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c241, some c255, some c251, some c416, some c35, some c406, some c184, some c62, some c106, some c260, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 57) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c241, c255, c251, c416, c35, c406, c184, c62, c106, c260] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c416 := derived416 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c406 := derived406 a h
  have h6 : Entails.eval a c184 := h 183 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨34, by decide⟩, false), (⟨36, by decide⟩, true), (⟨25, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨14, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c184, some c190, some c171, some c144, some c151, some c264, some c260, some c188, some c191, some c135, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 57) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c184, c190, c171, c144, c151, c264, c260, c188, c191, c135] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c184 := h 183 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c188 := h 187 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨22, by decide⟩, true), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c208, some c34, some c81, some c31, some c96, some c220, some c352, some c218, some c418, some c213, some c419, some c127, some c307, some c305, some c194, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 57) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c111, c208, c34, c81, c31, c96, c220, c352, c218, c418, c213, c419, c127, c307, c305, c194] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c352 := h 351 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c418 := derived418 a h
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c419 := derived419 a h
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c307 := h 306 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c307, some c305, some c194, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 57) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c307, c305, c194] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨40, by decide⟩, true), (⟨22, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c213, some c111, some c208, some c127, some c421, some c125, some c4, some c157, some c316, some c343, some c344, some c147, some c66, some c3, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 57) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c213, c111, c208, c127, c421, c125, c4, c157, c316, c343, c344, c147, c66, c3] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c213 := h 212 (by decide)
  have h1 : Entails.eval a c111 := h 110 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c421 := derived421 a h
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨39, by decide⟩, false), (⟨40, by decide⟩, true), (⟨22, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c111, some c213, some c422, some c184, some c190, some c125, some c144, some c419, some c344, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p423 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 57) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c111, c213, c422, c184, c190, c125, c144, c419, c344] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c111 := h 110 (by decide)
  have h1 : Entails.eval a c213 := h 212 (by decide)
  have h2 : Entails.eval a c422 := derived422 a h
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c419 := derived419 a h
  have h8 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false), (⟨38, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c184, some c406, some c205, some c106, some c62, some c343, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p424 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 57) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c163, c184, c406, c205, c106, c62, c343] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c406 := derived406 a h
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c383, some c379, some c391, some c208, some c111, some c417, some c59, some c210, some c325, some c420, some c423, some c241, some c255, some c257, some c25, some c35, some c220, some c352, some c218, some c251, some c424, some c127, some c108, some c305, some c265, some c125, some c62, some c4, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p425 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 57) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c396, c383, c379, c391, c208, c111, c417, c59, c210, c325, c420, c423, c241, c255, c257, c25, c35, c220, c352, c218, c251, c424, c127, c108, c305, c265, c125, c62, c4] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c396 := derived396 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c391 := derived391 a h
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c417 := derived417 a h
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c420 := derived420 a h
  have h11 : Entails.eval a c423 := derived423 a h
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c255 := h 254 (by decide)
  have h14 : Entails.eval a c257 := h 256 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c35 := h 34 (by decide)
  have h17 : Entails.eval a c220 := h 219 (by decide)
  have h18 : Entails.eval a c352 := h 351 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  have h20 : Entails.eval a c251 := h 250 (by decide)
  have h21 : Entails.eval a c424 := derived424 a h
  have h22 : Entails.eval a c127 := h 126 (by decide)
  have h23 : Entails.eval a c108 := h 107 (by decide)
  have h24 : Entails.eval a c305 := h 304 (by decide)
  have h25 : Entails.eval a c265 := h 264 (by decide)
  have h26 : Entails.eval a c125 := h 124 (by decide)
  have h27 : Entails.eval a c62 := h 61 (by decide)
  have h28 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c426 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c124, some c270, some c186, some c108, some c115, some c252, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p426 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 57) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c105, c124, c270, c186, c108, c115, c252] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨42, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c252, some c26, some c223, some c54, some c365, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p427 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 57) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c108, c252, c26, c223, c54, c365] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c252 := h 251 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨31, by decide⟩, false), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c125, some c261, some c106, some c281, some c20, some c52, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p428 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 57) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c125, c261, c106, c281, c20, c52] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c270, some c202, some c428, some c426, some c16, some c4, some c34, some c71, some c281, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p429 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 57) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c210, c270, c202, c428, c426, c16, c4, c34, c71, c281] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c428 := derived428 a h
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c208, some c57, some c317, some c427, some c270, some c429, some c105, some c145, some c189, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p430 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 57) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c210, c208, c57, c317, c427, c270, c429, c105, c145, c189] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c427 := derived427 a h
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c429 := derived429 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c425, some c363, some c208, some c249, some c210, some c248, some c396, some c383, some c379, some c127, some c176, some c430, some c334, some c350, some c324, some c374, some c167, some c322, some c112, some c338, some c412, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p431 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 57) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c425, c363, c208, c249, c210, c248, c396, c383, c379, c127, c176, c430, c334, c350, c324, c374, c167, c322, c112, c338, c412] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c425 := derived425 a h
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c249 := h 248 (by decide)
  have h4 : Entails.eval a c210 := h 209 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c396 := derived396 a h
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c379 := h 378 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c430 := derived430 a h
  have h12 : Entails.eval a c334 := h 333 (by decide)
  have h13 : Entails.eval a c350 := h 349 (by decide)
  have h14 : Entails.eval a c324 := h 323 (by decide)
  have h15 : Entails.eval a c374 := h 373 (by decide)
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c322 := h 321 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c338 := h 337 (by decide)
  have h20 : Entails.eval a c412 := derived412 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c432 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c350, some c324, some c374, some c230, some c322, some c256, some c251, some c344, some c211, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p432 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 57) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c210, c350, c324, c374, c230, c322, c256, c251, c344, c211] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c374 := h 373 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c167, some c230, some c171, some c251, some c158, some c223, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p433 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 57) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c374, c167, c230, c171, c251, c158, c223] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c251 := h 250 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨45, by decide⟩, true), (⟨15, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c251, some c222, some c158, some c125, some c115, some c305, some c307, some c190, some c187, some c134, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p434 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 57) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c256, c251, c222, c158, c125, c115, c305, c307, c190, c187, c134] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨34, by decide⟩, true), (⟨11, by decide⟩, false), (⟨38, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c190, some c187, some c145, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false))]
def p435 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 57) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c190, c187, c145] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c190 := h 189 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, true), (⟨24, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c230, some c122, some c166, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p436 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 57) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c230, c122, c166] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c230 := h 229 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c432, some c435, some c105, some c124, some c433, some c324, some c274, some c436, some c299, some c434, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p437 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 57) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c210, c432, c435, c105, c124, c433, c324, c274, c436, c299, c434] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c432 := derived432 a h
  have h2 : Entails.eval a c435 := derived435 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c433 := derived433 a h
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c434 := derived434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨15, by decide⟩, false), (⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c208, some c317, some c107, some c159, some c182, some c171, some c115, some c167, some c252, some c324, some c205, some c274, some c270, some c299, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p438 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 57) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c105, c208, c317, c107, c159, c182, c171, c115, c167, c252, c324, c205, c274, c270, c299] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c159 := h 158 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c324 := h 323 (by decide)
  have h11 : Entails.eval a c205 := h 204 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c124, some c438, some c334, some c350, some c268, some c126, some c324, some c182, some c167, some c171, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p439 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 57) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c105, c124, c438, c334, c350, c268, c126, c324, c182, c167, c171] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c438 := derived438 a h
  have h3 : Entails.eval a c334 := h 333 (by decide)
  have h4 : Entails.eval a c350 := h 349 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c182 := h 181 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨11, by decide⟩, false), (⟨56, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, false), (⟨38, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c439, some c190, some c187, some c435, some c117, some c350, some c324, some c152, some c167, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p440 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 57) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c439, c190, c187, c435, c117, c350, c324, c152, c167] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c439 := derived439 a h
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c435 := derived435 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c350 := h 349 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c383, some c379, some c425, some c363, some c208, some c248, some c249, some c210, some c431, some c437, some c440, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p441 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 57) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c396, c383, c379, c425, c363, c208, c248, c249, c210, c431, c437, c440] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c396 := derived396 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c431 := derived431 a h
  have h10 : Entails.eval a c437 := derived437 a h
  have h11 : Entails.eval a c440 := derived440 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c190, some c187, some c116, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p442 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 57) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c190, c187, c116] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c190 := h 189 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨40, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c442, some c100, some c116, some c184, some c125, some c144, some c260, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p443 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 57) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c442, c100, c116, c184, c125, c144, c260] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c442 := derived442 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c442, some c443, some c182, some c125, some c144, some c263, some c260, some c194, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p444 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 57) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c442, c443, c182, c125, c144, c263, c260, c194] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c442 := derived442 a h
  have h1 : Entails.eval a c443 := derived443 a h
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨42, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c442, some c444, some c107, some c182, some c159, some c125, some c144, some c421, some c345, some c36, some c205, some c27, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p445 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 57) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c442, c444, c107, c182, c159, c125, c144, c421, c345, c36, c205, c27] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c442 := derived442 a h
  have h1 : Entails.eval a c444 := derived444 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c159 := h 158 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c421 := derived421 a h
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c325, some c153, some c191, some c5, some c186, some c158, some c151, some c116, some c316, some c1, some c344, some c63, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p446 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 57) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c325, c153, c191, c5, c186, c158, c151, c116, c316, c1, c344, c63] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c325 := h 324 (by decide)
  have h1 : Entails.eval a c153 := h 152 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨46, by decide⟩, true), (⟨22, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c59, some c224, some c445, some c127, some c176, some c421, some c34, some c125, some c446, some c189, some c14, some c107, some c100, some c86, some c265, some c27, some c108, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p447 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 57) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c210, c59, c224, c445, c127, c176, c421, c34, c125, c446, c189, c14, c107, c100, c86, c265, c27, c108] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c224 := h 223 (by decide)
  have h3 : Entails.eval a c445 := derived445 a h
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c421 := derived421 a h
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c446 := derived446 a h
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  have h16 : Entails.eval a c27 := h 26 (by decide)
  have h17 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨26, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c294, some c299, some c305, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p448 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 57) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c294, c299, c305] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c294 := h 293 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c396, some c383, some c379, some c441, some c341, some c342, some c59, some c210, some c325, some c249, some c363, some c447, some c241, some c257, some c25, some c35, some c231, some c374, some c323, some c229, some c251, some c448, some c284, some c53, some c267, some c344, some c211, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p449 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 57) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c396, c383, c379, c441, c341, c342, c59, c210, c325, c249, c363, c447, c241, c257, c25, c35, c231, c374, c323, c229, c251, c448, c284, c53, c267, c344, c211] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c396 := derived396 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c441 := derived441 a h
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c342 := h 341 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c210 := h 209 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c249 := h 248 (by decide)
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c447 := derived447 a h
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c257 := h 256 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  have h16 : Entails.eval a c231 := h 230 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c323 := h 322 (by decide)
  have h19 : Entails.eval a c229 := h 228 (by decide)
  have h20 : Entails.eval a c251 := h 250 (by decide)
  have h21 : Entails.eval a c448 := derived448 a h
  have h22 : Entails.eval a c284 := h 283 (by decide)
  have h23 : Entails.eval a c53 := h 52 (by decide)
  have h24 : Entails.eval a c267 := h 266 (by decide)
  have h25 : Entails.eval a c344 := h 343 (by decide)
  have h26 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨26, by decide⟩, false), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c383, some c396, some c448, some c312, some c311, some c449, some c364, some c249, some c208, some c224, some c341, some c342, some c257, some c110, some c168, some c153, some c140, some c191, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p450 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 57) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c379, c383, c396, c448, c312, c311, c449, c364, c249, c208, c224, c341, c342, c257, c110, c168, c153, c140, c191] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c448 := derived448 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c449 := derived449 a h
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c249 := h 248 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c341 := h 340 (by decide)
  have h12 : Entails.eval a c342 := h 341 (by decide)
  have h13 : Entails.eval a c257 := h 256 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨26, by decide⟩, false), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c383, some c396, some c448, some c312, some c311, some c449, some c450, some c105, some c200, some c168, some c110, some c256, some c259, some c225, some c202, some c290, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p451 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 57) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c379, c383, c396, c448, c312, c311, c449, c450, c105, c200, c168, c110, c256, c259, c225, c202, c290] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c448 := derived448 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c449 := derived449 a h
  have h7 : Entails.eval a c450 := derived450 a h
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c452 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨21, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f452 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c221, some c259, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p452 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked452 : lratChecker f452 p452 = .success := by decide +kernel
theorem unsat452 : Unsatisfiable (PosFin 57) f452 := by
  apply lratCheckerSound f452 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p452
  · intro a ha; simp [p452] at ha; subst a; trivial
  · exact checked452
theorem derived452 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c452 := by
  apply localUnsat_implies_entails f452 [c200, c221, c259] c452 unsat452 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c453 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨26, by decide⟩, false), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f453 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c383, some c396, some c448, some c312, some c311, some c449, some c364, some c451, some c324, some c207, some c341, some c342, some c452, some c249, some c257, some c224, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p453 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked453 : lratChecker f453 p453 = .success := by decide +kernel
theorem unsat453 : Unsatisfiable (PosFin 57) f453 := by
  apply lratCheckerSound f453 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p453
  · intro a ha; simp [p453] at ha; subst a; trivial
  · exact checked453
theorem derived453 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c453 := by
  apply localUnsat_implies_entails f453 [c379, c383, c396, c448, c312, c311, c449, c364, c451, c324, c207, c341, c342, c452, c249, c257, c224] c453 unsat453 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c448 := derived448 a h
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c449 := derived449 a h
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c451 := derived451 a h
  have h9 : Entails.eval a c324 := h 323 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c341 := h 340 (by decide)
  have h12 : Entails.eval a c342 := h 341 (by decide)
  have h13 : Entails.eval a c452 := derived452 a h
  have h14 : Entails.eval a c249 := h 248 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c454 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨45, by decide⟩, true), (⟨18, by decide⟩, false), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f454 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c249, some c257, some c231, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p454 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked454 : lratChecker f454 p454 = .success := by decide +kernel
theorem unsat454 : Unsatisfiable (PosFin 57) f454 := by
  apply lratCheckerSound f454 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p454
  · intro a ha; simp [p454] at ha; subst a; trivial
  · exact checked454
theorem derived454 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c454 := by
  apply localUnsat_implies_entails f454 [c249, c257, c231] c454 unsat454 (by rfl) a
  have h0 : Entails.eval a c249 := h 248 (by decide)
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c455 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f455 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c449, some c364, some c454, some c221, some c452, some c248, some c231, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p455 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked455 : lratChecker f455 p455 = .success := by decide +kernel
theorem unsat455 : Unsatisfiable (PosFin 57) f455 := by
  apply lratCheckerSound f455 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p455
  · intro a ha; simp [p455] at ha; subst a; trivial
  · exact checked455
theorem derived455 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c455 := by
  apply localUnsat_implies_entails f455 [c449, c364, c454, c221, c452, c248, c231] c455 unsat455 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c454 := derived454 a h
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c452 := derived452 a h
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c456 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f456 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c221, some c23, some c245, some c37, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p456 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked456 : lratChecker f456 p456 = .success := by decide +kernel
theorem unsat456 : Unsatisfiable (PosFin 57) f456 := by
  apply lratCheckerSound f456 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p456
  · intro a ha; simp [p456] at ha; subst a; trivial
  · exact checked456
theorem derived456 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c456 := by
  apply localUnsat_implies_entails f456 [c200, c221, c23, c245, c37] c456 unsat456 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c457 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f457 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c449, some c364, some c396, some c383, some c379, some c448, some c311, some c312, some c453, some c267, some c317, some c204, some c53, some c341, some c342, some c318, some c455, some c374, some c456, some c249, some c25, some c229, some c49, some c23, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p457 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked457 : lratChecker f457 p457 = .success := by decide +kernel
theorem unsat457 : Unsatisfiable (PosFin 57) f457 := by
  apply lratCheckerSound f457 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p457
  · intro a ha; simp [p457] at ha; subst a; trivial
  · exact checked457
theorem derived457 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c457 := by
  apply localUnsat_implies_entails f457 [c449, c364, c396, c383, c379, c448, c311, c312, c453, c267, c317, c204, c53, c341, c342, c318, c455, c374, c456, c249, c25, c229, c49, c23] c457 unsat457 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c448 := derived448 a h
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c453 := derived453 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c318 := h 317 (by decide)
  have h16 : Entails.eval a c455 := derived455 a h
  have h17 : Entails.eval a c374 := h 373 (by decide)
  have h18 : Entails.eval a c456 := derived456 a h
  have h19 : Entails.eval a c249 := h 248 (by decide)
  have h20 : Entails.eval a c25 := h 24 (by decide)
  have h21 : Entails.eval a c229 := h 228 (by decide)
  have h22 : Entails.eval a c49 := h 48 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c458 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f458 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c81, some c416, some c8, some c182, some c171, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p458 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked458 : lratChecker f458 p458 = .success := by decide +kernel
theorem unsat458 : Unsatisfiable (PosFin 57) f458 := by
  apply lratCheckerSound f458 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p458
  · intro a ha; simp [p458] at ha; subst a; trivial
  · exact checked458
theorem derived458 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c458 := by
  apply localUnsat_implies_entails f458 [c34, c81, c416, c8, c182, c171] c458 unsat458 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c416 := derived416 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c459 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f459 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c458, some c89, some c1, some c86, some c171, some c8, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p459 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked459 : lratChecker f459 p459 = .success := by decide +kernel
theorem unsat459 : Unsatisfiable (PosFin 57) f459 := by
  apply lratCheckerSound f459 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p459
  · intro a ha; simp [p459] at ha; subst a; trivial
  · exact checked459
theorem derived459 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c459 := by
  apply localUnsat_implies_entails f459 [c458, c89, c1, c86, c171, c8] c459 unsat459 (by rfl) a
  have h0 : Entails.eval a c458 := derived458 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c460 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f460 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c126, some c459, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p460 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked460 : lratChecker f460 p460 = .success := by decide +kernel
theorem unsat460 : Unsatisfiable (PosFin 57) f460 := by
  apply lratCheckerSound f460 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p460
  · intro a ha; simp [p460] at ha; subst a; trivial
  · exact checked460
theorem derived460 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c460 := by
  apply localUnsat_implies_entails f460 [c35, c126, c459] c460 unsat460 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c459 := derived459 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c461 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f461 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c249, some c241, some c224, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p461 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked461 : lratChecker f461 p461 = .success := by decide +kernel
theorem unsat461 : Unsatisfiable (PosFin 57) f461 := by
  apply lratCheckerSound f461 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p461
  · intro a ha; simp [p461] at ha; subst a; trivial
  · exact checked461
theorem derived461 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c461 := by
  apply localUnsat_implies_entails f461 [c249, c241, c224] c461 unsat461 (by rfl) a
  have h0 : Entails.eval a c249 := h 248 (by decide)
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c462 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f462 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c187, some c189, some c176, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p462 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked462 : lratChecker f462 p462 = .success := by decide +kernel
theorem unsat462 : Unsatisfiable (PosFin 57) f462 := by
  apply lratCheckerSound f462 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p462
  · intro a ha; simp [p462] at ha; subst a; trivial
  · exact checked462
theorem derived462 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c462 := by
  apply localUnsat_implies_entails f462 [c187, c189, c176] c462 unsat462 (by rfl) a
  have h0 : Entails.eval a c187 := h 186 (by decide)
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c463 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f463 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c334, some c317, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p463 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked463 : lratChecker f463 p463 = .success := by decide +kernel
theorem unsat463 : Unsatisfiable (PosFin 57) f463 := by
  apply lratCheckerSound f463 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p463
  · intro a ha; simp [p463] at ha; subst a; trivial
  · exact checked463
theorem derived463 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c463 := by
  apply localUnsat_implies_entails f463 [c342, c334, c317] c463 unsat463 (by rfl) a
  have h0 : Entails.eval a c342 := h 341 (by decide)
  have h1 : Entails.eval a c334 := h 333 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c464 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨22, by decide⟩, true), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f464 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c171, some c176, some c184, some c185, some c121, some c123, some c256, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p464 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked464 : lratChecker f464 p464 = .success := by decide +kernel
theorem unsat464 : Unsatisfiable (PosFin 57) f464 := by
  apply lratCheckerSound f464 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p464
  · intro a ha; simp [p464] at ha; subst a; trivial
  · exact checked464
theorem derived464 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c464 := by
  apply localUnsat_implies_entails f464 [c171, c176, c184, c185, c121, c123, c256] c464 unsat464 (by rfl) a
  have h0 : Entails.eval a c171 := h 170 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c465 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f465 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c462, some c379, some c317, some c341, some c221, some c146, some c248, some c464, some c168, some c231, some c24, some c81, some c86, some c79, some c91, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p465 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked465 : lratChecker f465 p465 = .success := by decide +kernel
theorem unsat465 : Unsatisfiable (PosFin 57) f465 := by
  apply lratCheckerSound f465 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p465
  · intro a ha; simp [p465] at ha; subst a; trivial
  · exact checked465
theorem derived465 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c465 := by
  apply localUnsat_implies_entails f465 [c113, c462, c379, c317, c341, c221, c146, c248, c464, c168, c231, c24, c81, c86, c79, c91] c465 unsat465 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c462 := derived462 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c341 := h 340 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c464 := derived464 a h
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c231 := h 230 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c466 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f466 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c81, some c86, some c79, some c91, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p466 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked466 : lratChecker f466 p466 = .success := by decide +kernel
theorem unsat466 : Unsatisfiable (PosFin 57) f466 := by
  apply lratCheckerSound f466 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p466
  · intro a ha; simp [p466] at ha; subst a; trivial
  · exact checked466
theorem derived466 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c466 := by
  apply localUnsat_implies_entails f466 [c81, c86, c79, c91] c466 unsat466 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c467 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨34, by decide⟩, false), (⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨40, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f467 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c466, some c96, some c24, some c95, some c207, some c67, some c349, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p467 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked467 : lratChecker f467 p467 = .success := by decide +kernel
theorem unsat467 : Unsatisfiable (PosFin 57) f467 := by
  apply lratCheckerSound f467 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p467
  · intro a ha; simp [p467] at ha; subst a; trivial
  · exact checked467
theorem derived467 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c467 := by
  apply localUnsat_implies_entails f467 [c466, c96, c24, c95, c207, c67, c349] c467 unsat467 (by rfl) a
  have h0 : Entails.eval a c466 := derived466 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c468 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨13, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f468 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c123, some c248, some c221, some c202, some c273, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p468 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked468 : lratChecker f468 p468 = .success := by decide +kernel
theorem unsat468 : Unsatisfiable (PosFin 57) f468 := by
  apply lratCheckerSound f468 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p468
  · intro a ha; simp [p468] at ha; subst a; trivial
  · exact checked468
theorem derived468 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c468 := by
  apply localUnsat_implies_entails f468 [c110, c123, c248, c221, c202, c273] c468 unsat468 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c469 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨18, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f469 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c379, some c465, some c467, some c168, some c171, some c176, some c129, some c184, some c291, some c468, some c24, some c81, some c86, some c89, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p469 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked469 : lratChecker f469 p469 = .success := by decide +kernel
theorem unsat469 : Unsatisfiable (PosFin 57) f469 := by
  apply lratCheckerSound f469 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p469
  · intro a ha; simp [p469] at ha; subst a; trivial
  · exact checked469
theorem derived469 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c469 := by
  apply localUnsat_implies_entails f469 [c113, c379, c465, c467, c168, c171, c176, c129, c184, c291, c468, c24, c81, c86, c89] c469 unsat469 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c465 := derived465 a h
  have h3 : Entails.eval a c467 := derived467 a h
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c184 := h 183 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c468 := derived468 a h
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c470 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨43, by decide⟩, true), (⟨13, by decide⟩, true), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f470 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c462, some c176, some c379, some c171, some c184, some c134, some c129, some c100, some c460, some c349, some c344, some c332, some c152, some c212, some c341, some c250, some c221, some c205, some c248, some c269, some c464, some c298, some c135, some c314, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p470 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked470 : lratChecker f470 p470 = .success := by decide +kernel
theorem unsat470 : Unsatisfiable (PosFin 57) f470 := by
  apply lratCheckerSound f470 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p470
  · intro a ha; simp [p470] at ha; subst a; trivial
  · exact checked470
theorem derived470 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c470 := by
  apply localUnsat_implies_entails f470 [c113, c462, c176, c379, c171, c184, c134, c129, c100, c460, c349, c344, c332, c152, c212, c341, c250, c221, c205, c248, c269, c464, c298, c135, c314] c470 unsat470 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c462 := derived462 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c460 := derived460 a h
  have h10 : Entails.eval a c349 := h 348 (by decide)
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c212 := h 211 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c250 := h 249 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c205 := h 204 (by decide)
  have h19 : Entails.eval a c248 := h 247 (by decide)
  have h20 : Entails.eval a c269 := h 268 (by decide)
  have h21 : Entails.eval a c464 := derived464 a h
  have h22 : Entails.eval a c298 := h 297 (by decide)
  have h23 : Entails.eval a c135 := h 134 (by decide)
  have h24 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c471 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨26, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f471 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c462, some c100, some c379, some c171, some c176, some c129, some c184, some c164, some c134, some c470, some c219, some c256, some c123, some c468, some c291, some c313, some c227, some c36, some c26, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p471 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked471 : lratChecker f471 p471 = .success := by decide +kernel
theorem unsat471 : Unsatisfiable (PosFin 57) f471 := by
  apply lratCheckerSound f471 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p471
  · intro a ha; simp [p471] at ha; subst a; trivial
  · exact checked471
theorem derived471 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c471 := by
  apply localUnsat_implies_entails f471 [c113, c462, c100, c379, c171, c176, c129, c184, c164, c134, c470, c219, c256, c123, c468, c291, c313, c227, c36, c26] c471 unsat471 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c462 := derived462 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c470 := derived470 a h
  have h11 : Entails.eval a c219 := h 218 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c468 := derived468 a h
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c227 := h 226 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c472 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨45, by decide⟩, true), (⟨13, by decide⟩, false), (⟨34, by decide⟩, false), (⟨40, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f472 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c349, some c67, some c150, some c12, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p472 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked472 : lratChecker f472 p472 = .success := by decide +kernel
theorem unsat472 : Unsatisfiable (PosFin 57) f472 := by
  apply lratCheckerSound f472 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p472
  · intro a ha; simp [p472] at ha; subst a; trivial
  · exact checked472
theorem derived472 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c472 := by
  apply localUnsat_implies_entails f472 [c324, c349, c67, c150, c12] c472 unsat472 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c473 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false), (⟨45, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f473 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c221, some c69, some c248, some c30, some c231, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p473 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked473 : lratChecker f473 p473 = .success := by decide +kernel
theorem unsat473 : Unsatisfiable (PosFin 57) f473 := by
  apply lratCheckerSound f473 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p473
  · intro a ha; simp [p473] at ha; subst a; trivial
  · exact checked473
theorem derived473 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c473 := by
  apply localUnsat_implies_entails f473 [c221, c69, c248, c30, c231] c473 unsat473 (by rfl) a
  have h0 : Entails.eval a c221 := h 220 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c474 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f474 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c449, some c364, some c396, some c383, some c379, some c457, some c460, some c461, some c463, some c113, some c462, some c100, some c469, some c53, some c72, some c471, some c168, some c466, some c14, some c473, some c341, some c324, some c472, some c349, some c190, some c219, some c67, some c239, some c12, some c175, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p474 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked474 : lratChecker f474 p474 = .success := by decide +kernel
theorem unsat474 : Unsatisfiable (PosFin 57) f474 := by
  apply lratCheckerSound f474 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p474
  · intro a ha; simp [p474] at ha; subst a; trivial
  · exact checked474
theorem derived474 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c474 := by
  apply localUnsat_implies_entails f474 [c449, c364, c396, c383, c379, c457, c460, c461, c463, c113, c462, c100, c469, c53, c72, c471, c168, c466, c14, c473, c341, c324, c472, c349, c190, c219, c67, c239, c12, c175] c474 unsat474 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c457 := derived457 a h
  have h6 : Entails.eval a c460 := derived460 a h
  have h7 : Entails.eval a c461 := derived461 a h
  have h8 : Entails.eval a c463 := derived463 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c462 := derived462 a h
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c469 := derived469 a h
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c471 := derived471 a h
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c466 := derived466 a h
  have h18 : Entails.eval a c14 := h 13 (by decide)
  have h19 : Entails.eval a c473 := derived473 a h
  have h20 : Entails.eval a c341 := h 340 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c472 := derived472 a h
  have h23 : Entails.eval a c349 := h 348 (by decide)
  have h24 : Entails.eval a c190 := h 189 (by decide)
  have h25 : Entails.eval a c219 := h 218 (by decide)
  have h26 : Entails.eval a c67 := h 66 (by decide)
  have h27 : Entails.eval a c239 := h 238 (by decide)
  have h28 : Entails.eval a c12 := h 11 (by decide)
  have h29 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c475 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨26, by decide⟩, false), (⟨45, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f475 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c311, some c49, some c12, some c95, some c98, some c102, some c51, some c28, some c207, some c267, some c273, some c63, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false))]
def p475 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked475 : lratChecker f475 p475 = .success := by decide +kernel
theorem unsat475 : Unsatisfiable (PosFin 57) f475 := by
  apply lratCheckerSound f475 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p475
  · intro a ha; simp [p475] at ha; subst a; trivial
  · exact checked475
theorem derived475 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c475 := by
  apply localUnsat_implies_entails f475 [c311, c49, c12, c95, c98, c102, c51, c28, c207, c267, c273, c63] c475 unsat475 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c273 := h 272 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c476 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨5, by decide⟩, false), (⟨26, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f476 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c475, some c14, some c105, some c249, some c31, some c231, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p476 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked476 : lratChecker f476 p476 = .success := by decide +kernel
theorem unsat476 : Unsatisfiable (PosFin 57) f476 := by
  apply lratCheckerSound f476 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p476
  · intro a ha; simp [p476] at ha; subst a; trivial
  · exact checked476
theorem derived476 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c476 := by
  apply localUnsat_implies_entails f476 [c475, c14, c105, c249, c31, c231] c476 unsat476 (by rfl) a
  have h0 : Entails.eval a c475 := derived475 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c249 := h 248 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c477 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f477 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c249, some c454, some c116, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p477 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked477 : lratChecker f477 p477 = .success := by decide +kernel
theorem unsat477 : Unsatisfiable (PosFin 57) f477 := by
  apply lratCheckerSound f477 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p477
  · intro a ha; simp [p477] at ha; subst a; trivial
  · exact checked477
theorem derived477 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c477 := by
  apply localUnsat_implies_entails f477 [c249, c454, c116] c477 unsat477 (by rfl) a
  have h0 : Entails.eval a c249 := h 248 (by decide)
  have h1 : Entails.eval a c454 := derived454 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c478 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨45, by decide⟩, true), (⟨46, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f478 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c231, some c442, some c256, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false))]
def p478 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked478 : lratChecker f478 p478 = .success := by decide +kernel
theorem unsat478 : Unsatisfiable (PosFin 57) f478 := by
  apply lratCheckerSound f478 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p478
  · intro a ha; simp [p478] at ha; subst a; trivial
  · exact checked478
theorem derived478 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c478 := by
  apply localUnsat_implies_entails f478 [c231, c442, c256] c478 unsat478 (by rfl) a
  have h0 : Entails.eval a c231 := h 230 (by decide)
  have h1 : Entails.eval a c442 := derived442 a h
  have h2 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c479 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨32, by decide⟩, true), (⟨26, by decide⟩, false), (⟨45, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f479 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c251, some c222, some c193, some c277, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p479 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked479 : lratChecker f479 p479 = .success := by decide +kernel
theorem unsat479 : Unsatisfiable (PosFin 57) f479 := by
  apply lratCheckerSound f479 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p479
  · intro a ha; simp [p479] at ha; subst a; trivial
  · exact checked479
theorem derived479 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c479 := by
  apply localUnsat_implies_entails f479 [c256, c251, c222, c193, c277] c479 unsat479 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c480 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f480 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c383, some c396, some c449, some c364, some c474, some c358, some c372, some c460, some c466, some c285, some c448, some c311, some c476, some c171, some c176, some c182, some c184, some c477, some c105, some c200, some c478, some c248, some c479, some c107, some c267, some c152, some c341, some c342, some c221, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p480 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked480 : lratChecker f480 p480 = .success := by decide +kernel
theorem unsat480 : Unsatisfiable (PosFin 57) f480 := by
  apply lratCheckerSound f480 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p480
  · intro a ha; simp [p480] at ha; subst a; trivial
  · exact checked480
theorem derived480 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c480 := by
  apply localUnsat_implies_entails f480 [c379, c383, c396, c449, c364, c474, c358, c372, c460, c466, c285, c448, c311, c476, c171, c176, c182, c184, c477, c105, c200, c478, c248, c479, c107, c267, c152, c341, c342, c221] c480 unsat480 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c396 := derived396 a h
  have h3 : Entails.eval a c449 := derived449 a h
  have h4 : Entails.eval a c364 := h 363 (by decide)
  have h5 : Entails.eval a c474 := derived474 a h
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c460 := derived460 a h
  have h9 : Entails.eval a c466 := derived466 a h
  have h10 : Entails.eval a c285 := h 284 (by decide)
  have h11 : Entails.eval a c448 := derived448 a h
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c476 := derived476 a h
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c477 := derived477 a h
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c200 := h 199 (by decide)
  have h21 : Entails.eval a c478 := derived478 a h
  have h22 : Entails.eval a c248 := h 247 (by decide)
  have h23 : Entails.eval a c479 := derived479 a h
  have h24 : Entails.eval a c107 := h 106 (by decide)
  have h25 : Entails.eval a c267 := h 266 (by decide)
  have h26 : Entails.eval a c152 := h 151 (by decide)
  have h27 : Entails.eval a c341 := h 340 (by decide)
  have h28 : Entails.eval a c342 := h 341 (by decide)
  have h29 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c481 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, false), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f481 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c255, some c227, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p481 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked481 : lratChecker f481 p481 = .success := by decide +kernel
theorem unsat481 : Unsatisfiable (PosFin 57) f481 := by
  apply lratCheckerSound f481 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p481
  · intro a ha; simp [p481] at ha; subst a; trivial
  · exact checked481
theorem derived481 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c481 := by
  apply localUnsat_implies_entails f481 [c257, c255, c227] c481 unsat481 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c482 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f482 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c101, some c265, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p482 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked482 : lratChecker f482 p482 = .success := by decide +kernel
theorem unsat482 : Unsatisfiable (PosFin 57) f482 := by
  apply lratCheckerSound f482 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p482
  · intro a ha; simp [p482] at ha; subst a; trivial
  · exact checked482
theorem derived482 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c482 := by
  apply localUnsat_implies_entails f482 [c205, c101, c265] c482 unsat482 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c483 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f483 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c127, some c101, some c243, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p483 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked483 : lratChecker f483 p483 = .success := by decide +kernel
theorem unsat483 : Unsatisfiable (PosFin 57) f483 := by
  apply lratCheckerSound f483 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p483
  · intro a ha; simp [p483] at ha; subst a; trivial
  · exact checked483
theorem derived483 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c483 := by
  apply localUnsat_implies_entails f483 [c127, c101, c243] c483 unsat483 (by rfl) a
  have h0 : Entails.eval a c127 := h 126 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c484 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨44, by decide⟩, true), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f484 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c227, some c226, some c120, some c259, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p484 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked484 : lratChecker f484 p484 = .success := by decide +kernel
theorem unsat484 : Unsatisfiable (PosFin 57) f484 := by
  apply lratCheckerSound f484 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p484
  · intro a ha; simp [p484] at ha; subst a; trivial
  · exact checked484
theorem derived484 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c484 := by
  apply localUnsat_implies_entails f484 [c227, c226, c120, c259] c484 unsat484 (by rfl) a
  have h0 : Entails.eval a c227 := h 226 (by decide)
  have h1 : Entails.eval a c226 := h 225 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived484

end CochromaticTwenty.Certificates.B16_7_0
