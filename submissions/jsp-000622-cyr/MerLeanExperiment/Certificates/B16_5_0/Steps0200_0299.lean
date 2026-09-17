import MerLeanExperiment.Certificates.B16_5_0.Steps0100_0199

/-! Generated from the actual pinned b16_5_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_5_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c557 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c505, some c555, some c116, some c109, some c337, some c354, some c523, some c200, some c125, some c556, some c27, some c9, some c404, some c25, some c317, some c231, some c169, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c505, c555, c116, c109, c337, c354, c523, c200, c125, c556, c27, c9, c404, c25, c317, c231, c169] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c555 := derived555 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c337 := h 336 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c523 := derived523 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c404 := derived404 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c317 := h 316 (by decide)
  have h15 : Entails.eval a c231 := h 230 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c557, some c505, some c555, some c109, some c534, some c116, some c354, some c140, some c273, some c157, some c113, some c125, some c210, some c226, some c133, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c557, c505, c555, c109, c534, c116, c354, c140, c273, c157, c113, c125, c210, c226, c133] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c505 := derived505 a h
  have h2 : Entails.eval a c555 := derived555 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c534 := derived534 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c125 := h 124 (by decide)
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c226 := h 225 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c505, some c523, some c555, some c116, some c109, some c354, some c337, some c557, some c140, some c113, some c558, some c203, some c186, some c129, some c355, some c439, some c11, some c28, some c52, some c210, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c505, c523, c555, c116, c109, c354, c337, c557, c140, c113, c558, c203, c186, c129, c355, c439, c11, c28, c52, c210] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c523 := derived523 a h
  have h2 : Entails.eval a c555 := derived555 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c337 := h 336 (by decide)
  have h7 : Entails.eval a c557 := derived557 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c558 := derived558 a h
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c129 := h 128 (by decide)
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c439 := derived439 a h
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c28 := h 27 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c214, some c149, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c210, c214, c149] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨19, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c560, some c45, some c226, some c230, some c166, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c560, c45, c226, c230, c166] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c560 := derived560 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c226 := h 225 (by decide)
  have h3 : Entails.eval a c230 := h 229 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c129, some c15, some c42, some c34, some c99, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c129, c15, c42, c34, c99] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c129 := h 128 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c255, some c260, some c33, some c119, some c245, some c11, some c200, some c203, some c561, some c110, some c117, some c326, some c351, some c349, some c254, some c90, some c562, some c18, some c264, some c99, some c98, some c40, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c559, c255, c260, c33, c119, c245, c11, c200, c203, c561, c110, c117, c326, c351, c349, c254, c90, c562, c18, c264, c99, c98, c40] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c561 := derived561 a h
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c326 := h 325 (by decide)
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c349 := h 348 (by decide)
  have h15 : Entails.eval a c254 := h 253 (by decide)
  have h16 : Entails.eval a c90 := h 89 (by decide)
  have h17 : Entails.eval a c562 := derived562 a h
  have h18 : Entails.eval a c18 := h 17 (by decide)
  have h19 : Entails.eval a c264 := h 263 (by decide)
  have h20 : Entails.eval a c99 := h 98 (by decide)
  have h21 : Entails.eval a c98 := h 97 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c117, some c332, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c110, c117, c332] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c332, some c144, some c186, some c275, some c328, some c45, some c157, some c308, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c332, c144, c186, c275, c328, c45, c157, c308] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c332 := h 331 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨51, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c565, some c161, some c176, some c328, some c140, some c186, some c271, some c312, some c45, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c565, c161, c176, c328, c140, c186, c271, c312, c45] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c565 := derived565 a h
  have h1 : Entails.eval a c161 := h 160 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c271 := h 270 (by decide)
  have h7 : Entails.eval a c312 := h 311 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c33, some c119, some c11, some c200, some c203, some c28, some c20, some c566, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c559, c33, c119, c11, c200, c203, c28, c20, c566] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c566 := derived566 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c563, some c567, some c28, some c20, some c564, some c566, some c200, some c195, some c146, some c185, some c213, some c221, some c347, some c349, some c284, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c559, c563, c567, c28, c20, c564, c566, c200, c195, c146, c185, c213, c221, c347, c349, c284] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c564 := derived564 a h
  have h6 : Entails.eval a c566 := derived566 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c221 := h 220 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c349 := h 348 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c213, some c221, some c149, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c213, c221, c149] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c213 := h 212 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c57, some c146, some c11, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c559, c57, c146, c11] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c563, some c567, some c568, some c570, some c213, some c569, some c132, some c149, some c110, some c229, some c281, some c72, some c163, some c11, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c563, c567, c568, c570, c213, c569, c132, c149, c110, c229, c281, c72, c163, c11] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c563 := derived563 a h
  have h1 : Entails.eval a c567 := derived567 a h
  have h2 : Entails.eval a c568 := derived568 a h
  have h3 : Entails.eval a c570 := derived570 a h
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c569 := derived569 a h
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c229 := h 228 (by decide)
  have h10 : Entails.eval a c281 := h 280 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c563, some c567, some c568, some c570, some c213, some c571, some c200, some c195, some c6, some c185, some c51, some c44, some c303, some c229, some c165, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c559, c563, c567, c568, c570, c213, c571, c200, c195, c6, c185, c51, c44, c303, c229, c165] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c568 := derived568 a h
  have h4 : Entails.eval a c570 := derived570 a h
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c571 := derived571 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c303 := h 302 (by decide)
  have h14 : Entails.eval a c229 := h 228 (by decide)
  have h15 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c563, some c567, some c572, some c203, some c146, some c213, some c197, some c185, some c51, some c44, some c303, some c229, some c165, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c559, c563, c567, c572, c203, c146, c213, c197, c185, c51, c44, c303, c229, c165] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c572 := derived572 a h
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c563, some c567, some c572, some c203, some c146, some c213, some c197, some c185, some c140, some c132, some c303, some c229, some c165, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c559, c563, c567, c572, c203, c146, c213, c197, c185, c140, c132, c303, c229, c165] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c563 := derived563 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c572 := derived572 a h
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c132 := h 131 (by decide)
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c563, some c567, some c262, some c572, some c197, some c573, some c574, some c515, some c6, some c256, some c39, some c120, some c8, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c563, c567, c262, c572, c197, c573, c574, c515, c6, c256, c39, c120, c8] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c563 := derived563 a h
  have h1 : Entails.eval a c567 := derived567 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c572 := derived572 a h
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c573 := derived573 a h
  have h6 : Entails.eval a c574 := derived574 a h
  have h7 : Entails.eval a c515 := derived515 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c575, some c262, some c260, some c39, some c125, some c114, some c202, some c201, some c192, some c478, some c124, some c353, some c347, some c256, some c244, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c559, c575, c262, c260, c39, c125, c114, c202, c201, c192, c478, c124, c353, c347, c256, c244] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c192 := h 191 (by decide)
  have h10 : Entails.eval a c478 := derived478 a h
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c245, some c105, some c324, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c559, c245, c105, c324] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c245 := h 244 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c212, some c205, some c147, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c212, c205, c147] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c212 := h 211 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c119, some c202, some c33, some c9, some c575, some c125, some c114, some c107, some c261, some c124, some c196, some c577, some c578, some c44, some c51, some c228, some c308, some c169, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c559, c119, c202, c33, c9, c575, c125, c114, c107, c261, c124, c196, c577, c578, c44, c51, c228, c308, c169] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c575 := derived575 a h
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c577 := derived577 a h
  have h13 : Entails.eval a c578 := derived578 a h
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c308 := h 307 (by decide)
  have h18 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨2, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c210, some c152, some c133, some c212, some c226, some c109, some c67, some c273, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c575, c210, c152, c133, c212, c226, c109, c67, c273] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c212 := h 211 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c575, some c576, some c33, some c119, some c9, some c202, some c579, some c255, some c245, some c580, some c44, some c51, some c226, some c347, some c169, some c189, some c310, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c559, c575, c576, c33, c119, c9, c202, c579, c255, c245, c580, c44, c51, c226, c347, c169, c189, c310] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c576 := derived576 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c579 := derived579 a h
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c580 := derived580 a h
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c226 := h 225 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c347, some c189, some c141, some c210, some c132, some c226, some c310, some c169, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c575, c347, c189, c141, c210, c132, c226, c310, c169] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c210 := h 209 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c255, some c581, some c575, some c582, some c140, some c210, some c580, some c152, some c102, some c212, some c296, some c34, some c61, some c96, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c255, c581, c575, c582, c140, c210, c580, c152, c102, c212, c296, c34, c61, c96] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c581 := derived581 a h
  have h2 : Entails.eval a c575 := derived575 a h
  have h3 : Entails.eval a c582 := derived582 a h
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c580 := derived580 a h
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c212 := h 211 (by decide)
  have h10 : Entails.eval a c296 := h 295 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c581, some c575, some c210, some c133, some c62, some c226, some c212, some c157, some c22, some c273, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c581, c575, c210, c133, c62, c226, c212, c157, c22, c273] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c581 := derived581 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c119, some c33, some c581, some c255, some c245, some c583, some c15, some c584, some c140, some c132, some c347, some c226, some c89, some c76, some c310, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c559, c119, c33, c581, c255, c245, c583, c15, c584, c140, c132, c347, c226, c89, c76, c310] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c581 := derived581 a h
  have h4 : Entails.eval a c255 := h 254 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c583 := derived583 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c584 := derived584 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c132 := h 131 (by decide)
  have h11 : Entails.eval a c347 := h 346 (by decide)
  have h12 : Entails.eval a c226 := h 225 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨23, by decide⟩, false), (⟨52, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c347, some c353, some c245, some c93, some c259, some c332, some c23, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c559, c347, c353, c245, c93, c259, c332, c23] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c332 := h 331 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c119, some c33, some c575, some c585, some c114, some c581, some c107, some c566, some c17, some c15, some c39, some c261, some c252, some c124, some c204, some c126, some c586, some c140, some c187, some c212, some c356, some c54, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c559, c119, c33, c575, c585, c114, c581, c107, c566, c17, c15, c39, c261, c252, c124, c204, c126, c586, c140, c187, c212, c356, c54] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c585 := derived585 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c581 := derived581 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c566 := derived566 a h
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c126 := h 125 (by decide)
  have h17 : Entails.eval a c586 := derived586 a h
  have h18 : Entails.eval a c140 := h 139 (by decide)
  have h19 : Entails.eval a c187 := h 186 (by decide)
  have h20 : Entails.eval a c212 := h 211 (by decide)
  have h21 : Entails.eval a c356 := h 355 (by decide)
  have h22 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨43, by decide⟩, false), (⟨10, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c212, some c135, some c152, some c228, some c271, some c157, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c575, c212, c135, c152, c228, c271, c157] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c581, some c575, some c585, some c114, some c107, some c587, some c125, some c588, some c140, some c132, some c308, some c228, some c169, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c581, c575, c585, c114, c107, c587, c125, c588, c140, c132, c308, c228, c169] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c581 := derived581 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c587 := derived587 a h
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c588 := derived588 a h
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨40, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c146, some c163, some c276, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c559, c146, c163, c276] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c163 := h 162 (by decide)
  have h3 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c575, some c589, some c260, some c107, some c114, some c262, some c125, some c39, some c581, some c328, some c157, some c308, some c229, some c133, some c590, some c15, some c57, some c72, some c276, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c559, c575, c589, c260, c107, c114, c262, c125, c39, c581, c328, c157, c308, c229, c133, c590, c15, c57, c72, c276] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c589 := derived589 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c262 := h 261 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c581 := derived581 a h
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c308 := h 307 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c590 := derived590 a h
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c72 := h 71 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c575, some c581, some c589, some c262, some c260, some c39, some c125, some c591, some c140, some c213, some c57, some c146, some c15, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c559, c575, c581, c589, c262, c260, c39, c125, c591, c140, c213, c57, c146, c15] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c589 := derived589 a h
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c591 := derived591 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c103, some c100, some c575, some c260, some c114, some c213, some c44, some c51, some c60, some c308, some c298, some c133, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c592, c103, c100, c575, c260, c114, c213, c44, c51, c60, c308, c298, c133] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c298 := h 297 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨19, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c107, some c114, some c347, some c328, some c283, some c157, some c80, some c308, some c332, some c133, some c55, some c292, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c559, c107, c114, c347, c328, c283, c157, c80, c308, c332, c133, c55, c292] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c347 := h 346 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  have h9 : Entails.eval a c332 := h 331 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c575, some c260, some c107, some c114, some c592, some c100, some c103, some c593, some c146, some c202, some c594, some c140, some c86, some c349, some c332, some c283, some c70, some c290, some c312, some c133, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c559, c575, c260, c107, c114, c592, c100, c103, c593, c146, c202, c594, c140, c86, c349, c332, c283, c70, c290, c312, c133] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c592 := derived592 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c593 := derived593 a h
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c594 := derived594 a h
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c349 := h 348 (by decide)
  have h15 : Entails.eval a c332 := h 331 (by decide)
  have h16 : Entails.eval a c283 := h 282 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  have h18 : Entails.eval a c290 := h 289 (by decide)
  have h19 : Entails.eval a c312 := h 311 (by decide)
  have h20 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c57, some c213, some c575, some c260, some c107, some c114, some c140, some c132, some c308, some c229, some c133, some c72, some c276, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c559, c57, c213, c575, c260, c107, c114, c140, c132, c308, c229, c133, c72, c276] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c213 := h 212 (by decide)
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c132 := h 131 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨17, by decide⟩, true), (⟨52, by decide⟩, false), (⟨51, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c353, some c244, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c347, c353, c244] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c592, some c575, some c262, some c260, some c114, some c595, some c57, some c213, some c596, some c202, some c201, some c192, some c124, some c256, some c597, some c51, some c478, some c95, some c34, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c559, c592, c575, c262, c260, c114, c595, c57, c213, c596, c202, c201, c192, c124, c256, c597, c51, c478, c95, c34] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c575 := derived575 a h
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c595 := derived595 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c596 := derived596 a h
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c597 := derived597 a h
  have h16 : Entails.eval a c51 := h 50 (by decide)
  have h17 : Entails.eval a c478 := derived478 a h
  have h18 : Entails.eval a c95 := h 94 (by decide)
  have h19 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c592, some c598, some c33, some c103, some c575, some c349, some c245, some c255, some c256, some c107, some c124, some c332, some c204, some c23, some c126, some c259, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c559, c592, c598, c33, c103, c575, c349, c245, c255, c256, c107, c124, c332, c204, c23, c126, c259] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c575 := derived575 a h
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c332 := h 331 (by decide)
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c598, some c119, some c202, some c592, some c33, some c103, some c100, some c575, some c140, some c86, some c599, some c141, some c114, some c210, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c559, c598, c119, c202, c592, c33, c103, c100, c575, c140, c86, c599, c141, c114, c210] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c598 := derived598 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c592 := derived592 a h
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c575 := derived575 a h
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c599 := derived599 a h
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨13, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c600, some c598, some c33, some c119, some c15, some c592, some c103, some c100, some c575, some c141, some c114, some c255, some c210, some c245, some c60, some c348, some c214, some c252, some c42, some c261, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c559, c600, c598, c33, c119, c15, c592, c103, c100, c575, c141, c114, c255, c210, c245, c60, c348, c214, c252, c42, c261] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c600 := derived600 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c575 := derived575 a h
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c348 := h 347 (by decide)
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  have h19 : Entails.eval a c42 := h 41 (by decide)
  have h20 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c592, some c598, some c33, some c119, some c103, some c15, some c600, some c601, some c599, some c347, some c93, some c245, some c353, some c256, some c252, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c559, c592, c598, c33, c119, c103, c15, c600, c601, c599, c347, c93, c245, c353, c256, c252] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c600 := derived600 a h
  have h8 : Entails.eval a c601 := derived601 a h
  have h9 : Entails.eval a c599 := derived599 a h
  have h10 : Entails.eval a c347 := h 346 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c245 := h 244 (by decide)
  have h13 : Entails.eval a c353 := h 352 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c347, some c602, some c575, some c245, some c255, some c107, some c579, some c125, some c328, some c157, some c308, some c228, some c169, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c559, c347, c602, c575, c245, c255, c107, c579, c125, c328, c157, c308, c228, c169] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c602 := derived602 a h
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c579 := derived579 a h
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c602, some c575, some c262, some c260, some c125, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c602, c575, c262, c260, c125] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c602 := derived602 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c604, some c602, some c575, some c603, some c189, some c114, some c353, some c255, some c252, some c245, some c261, some c582, some c120, some c361, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c559, c604, c602, c575, c603, c189, c114, c353, c255, c252, c245, c261, c582, c120, c361] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c604 := derived604 a h
  have h2 : Entails.eval a c602 := derived602 a h
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c603 := derived603 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c582 := derived582 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c361 := derived361 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c575, some c592, some c602, some c604, some c33, some c100, some c605, some c51, some c580, some c107, some c579, some c125, some c588, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c559, c575, c592, c602, c604, c33, c100, c605, c51, c580, c107, c579, c125, c588] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c592 := derived592 a h
  have h3 : Entails.eval a c602 := derived602 a h
  have h4 : Entails.eval a c604 := derived604 a h
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c605 := derived605 a h
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c580 := derived580 a h
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c579 := derived579 a h
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c588 := derived588 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c27, some c113, some c33, some c119, some c9, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c606, c559, c27, c113, c33, c119, c9] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c27, some c113, some c9, some c57, some c200, some c607, some c107, some c125, some c219, some c135, some c152, some c235, some c276, some c404, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c606, c559, c27, c113, c9, c57, c200, c607, c107, c125, c219, c135, c152, c235, c276, c404] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c607 := derived607 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c276 := h 275 (by decide)
  have h15 : Entails.eval a c404 := derived404 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨13, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c607, some c27, some c113, some c200, some c9, some c57, some c608, some c215, some c152, some c133, some c219, some c231, some c109, some c404, some c279, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c606, c559, c607, c27, c113, c200, c9, c57, c608, c215, c152, c133, c219, c231, c109, c404, c279] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c607 := derived607 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c608 := derived608 a h
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  have h13 : Entails.eval a c231 := h 230 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  have h15 : Entails.eval a c404 := derived404 a h
  have h16 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c609, some c146, some c607, some c27, some c113, some c215, some c152, some c133, some c219, some c231, some c109, some c404, some c279, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c606, c559, c609, c146, c607, c27, c113, c215, c152, c133, c219, c231, c109, c404, c279] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c609 := derived609 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c607 := derived607 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c215 := h 214 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c231 := h 230 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c404 := derived404 a h
  have h14 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c609, some c146, some c607, some c610, some c107, some c125, some c219, some c135, some c152, some c235, some c590, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c559, c609, c146, c607, c610, c107, c125, c219, c135, c152, c235, c590] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c609 := derived609 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c607 := derived607 a h
  have h4 : Entails.eval a c610 := derived610 a h
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c590 := derived590 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c606, some c607, some c27, some c113, some c609, some c146, some c611, some c195, some c6, some c185, some c349, some c246, some c221, some c263, some c284, some c20, some c295, some c324, some c45, some c156, some c304, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c559, c606, c607, c27, c113, c609, c146, c611, c195, c6, c185, c349, c246, c221, c263, c284, c20, c295, c324, c45, c156, c304] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c607 := derived607 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c609 := derived609 a h
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c611 := derived611 a h
  have h8 : Entails.eval a c195 := h 194 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c20 := h 19 (by decide)
  have h17 : Entails.eval a c295 := h 294 (by decide)
  have h18 : Entails.eval a c324 := h 323 (by decide)
  have h19 : Entails.eval a c45 := h 44 (by decide)
  have h20 : Entails.eval a c156 := h 155 (by decide)
  have h21 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c606, some c113, some c612, some c202, some c201, some c192, some c607, some c27, some c195, some c6, some c185, some c349, some c350, some c246, some c247, some c263, some c259, some c20, some c105, some c324, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c559, c606, c113, c612, c202, c201, c192, c607, c27, c195, c6, c185, c349, c350, c246, c247, c263, c259, c20, c105, c324] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c612 := derived612 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c607 := derived607 a h
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c350 := h 349 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c259 := h 258 (by decide)
  have h18 : Entails.eval a c20 := h 19 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c606, some c113, some c612, some c202, some c201, some c192, some c146, some c607, some c349, some c350, some c324, some c246, some c194, some c247, some c221, some c259, some c144, some c105, some c199, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c559, c606, c113, c612, c202, c201, c192, c146, c607, c349, c350, c324, c246, c194, c247, c221, c259, c144, c105, c199] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c612 := derived612 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c607 := derived607 a h
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c350 := h 349 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c194 := h 193 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c221 := h 220 (by decide)
  have h16 : Entails.eval a c259 := h 258 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c606, some c613, some c113, some c612, some c202, some c201, some c192, some c27, some c8, some c107, some c124, some c614, some c185, some c1, some c84, some c26, some c356, some c258, some c247, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c559, c606, c613, c113, c612, c202, c201, c192, c27, c8, c107, c124, c614, c185, c1, c84, c26, c356, c258, c247] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c612 := derived612 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c614 := derived614 a h
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c26 := h 25 (by decide)
  have h17 : Entails.eval a c356 := h 355 (by decide)
  have h18 : Entails.eval a c258 := h 257 (by decide)
  have h19 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c607, some c27, some c113, some c612, some c202, some c201, some c8, some c146, some c192, some c613, some c615, some c263, some c215, some c246, some c133, some c349, some c231, some c185, some c171, some c1, some c84, some c26, some c314, some c223, some c73, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c606, c559, c607, c27, c113, c612, c202, c201, c8, c146, c192, c613, c615, c263, c215, c246, c133, c349, c231, c185, c171, c1, c84, c26, c314, c223, c73] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c607 := derived607 a h
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c612 := derived612 a h
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c192 := h 191 (by decide)
  have h11 : Entails.eval a c613 := derived613 a h
  have h12 : Entails.eval a c615 := derived615 a h
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c215 := h 214 (by decide)
  have h15 : Entails.eval a c246 := h 245 (by decide)
  have h16 : Entails.eval a c133 := h 132 (by decide)
  have h17 : Entails.eval a c349 := h 348 (by decide)
  have h18 : Entails.eval a c231 := h 230 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c171 := h 170 (by decide)
  have h21 : Entails.eval a c1 := h 0 (by decide)
  have h22 : Entails.eval a c84 := h 83 (by decide)
  have h23 : Entails.eval a c26 := h 25 (by decide)
  have h24 : Entails.eval a c314 := h 313 (by decide)
  have h25 : Entails.eval a c223 := h 222 (by decide)
  have h26 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c616, some c607, some c113, some c611, some c141, some c114, some c202, some c215, some c146, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c606, c559, c616, c607, c113, c611, c141, c114, c202, c215, c146] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c616 := derived616 a h
  have h3 : Entails.eval a c607 := derived607 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c113, some c27, some c607, some c616, some c617, some c200, some c6, some c146, some c52, some c28, some c215, some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c606, c559, c113, c27, c607, c616, c617, c200, c6, c146, c52, c28, c215] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c607 := derived607 a h
  have h5 : Entails.eval a c616 := derived616 a h
  have h6 : Entails.eval a c617 := derived617 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c618, some c559, some c195, some c6, some c185, some c19, some c36, some c348, some c323, some c103, some c97, some c192, some c79, some c201, some c345, some c174, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c606, c618, c559, c195, c6, c185, c19, c36, c348, c323, c103, c97, c192, c79, c201, c345, c174] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c618 := derived618 a h
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c195 := h 194 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c185 := h 184 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c348 := h 347 (by decide)
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c201 := h 200 (by decide)
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c618, some c606, some c619, some c122, some c197, some c10, some c185, some c36, some c31, some c348, some c100, some c351, some c192, some c92, some c194, some c94, some c13, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c559, c618, c606, c619, c122, c197, c10, c185, c36, c31, c348, c100, c351, c192, c92, c194, c94, c13] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c618 := derived618 a h
  have h2 : Entails.eval a c606 := derived606 a h
  have h3 : Entails.eval a c619 := derived619 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c100 := h 99 (by decide)
  have h12 : Entails.eval a c351 := h 350 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  have h14 : Entails.eval a c92 := h 91 (by decide)
  have h15 : Entails.eval a c194 := h 193 (by decide)
  have h16 : Entails.eval a c94 := h 93 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨19, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c559, some c606, some c119, some c146, some c263, some c215, some c620, some c52, some c347, some c185, some c195, some c197, some c122, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c618, c559, c606, c119, c146, c263, c215, c620, c52, c347, c185, c195, c197, c122] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c606 := derived606 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c620 := derived620 a h
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c347 := h 346 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c195 := h 194 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c559, some c606, some c621, some c200, some c203, some c106, some c122, some c263, some c257, some c33, some c245, some c11, some c347, some c348, some c323, some c52, some c88, some c18, some c214, some c98, some c144, some c90, some c351, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c618, c559, c606, c621, c200, c203, c106, c122, c263, c257, c33, c245, c11, c347, c348, c323, c52, c88, c18, c214, c98, c144, c90, c351] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c606 := derived606 a h
  have h3 : Entails.eval a c621 := derived621 a h
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c348 := h 347 (by decide)
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c52 := h 51 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c18 := h 17 (by decide)
  have h19 : Entails.eval a c214 := h 213 (by decide)
  have h20 : Entails.eval a c98 := h 97 (by decide)
  have h21 : Entails.eval a c144 := h 143 (by decide)
  have h22 : Entails.eval a c90 := h 89 (by decide)
  have h23 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨16, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c200, some c203, some c122, some c106, some c622, some c567, some c570, some c11, some c221, some c149, some c136, some c274, some c384, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c606, c200, c203, c122, c106, c622, c567, c570, c11, c221, c149, c136, c274, c384] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c622 := derived622 a h
  have h6 : Entails.eval a c567 := derived567 a h
  have h7 : Entails.eval a c570 := derived570 a h
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c384 := derived384 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c200, some c203, some c623, some c28, some c20, some c566, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c622, c200, c203, c623, c28, c20, c566] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c623 := derived623 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c566 := derived566 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c28, some c20, some c328, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c618, c28, c20, c328] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c622, some c567, some c624, some c146, some c106, some c625, some c620, some c221, some c185, some c197, some c2, some c149, some c136, some c26, some c50, some c267, some c224, some c66, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c606, c559, c622, c567, c624, c146, c106, c625, c620, c221, c185, c197, c2, c149, c136, c26, c50, c267, c224, c66] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c567 := derived567 a h
  have h4 : Entails.eval a c624 := derived624 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c625 := derived625 a h
  have h8 : Entails.eval a c620 := derived620 a h
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c2 := h 1 (by decide)
  have h13 : Entails.eval a c149 := h 148 (by decide)
  have h14 : Entails.eval a c136 := h 135 (by decide)
  have h15 : Entails.eval a c26 := h 25 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c267 := h 266 (by decide)
  have h18 : Entails.eval a c224 := h 223 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c559, some c622, some c567, some c624, some c146, some c106, some c625, some c620, some c221, some c149, some c136, some c274, some c237, some c163, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c606, c559, c622, c567, c624, c146, c106, c625, c620, c221, c149, c136, c274, c237, c163] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c559 := derived559 a h
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c567 := derived567 a h
  have h4 : Entails.eval a c624 := derived624 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c625 := derived625 a h
  have h8 : Entails.eval a c620 := derived620 a h
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c237 := h 236 (by decide)
  have h14 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c606, some c618, some c624, some c146, some c622, some c567, some c106, some c625, some c620, some c221, some c626, some c323, some c627, some c197, some c10, some c156, some c55, some c48, some c306, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c559, c606, c618, c624, c146, c622, c567, c106, c625, c620, c221, c626, c323, c627, c197, c10, c156, c55, c48, c306] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c618 := derived618 a h
  have h3 : Entails.eval a c624 := derived624 a h
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c622 := derived622 a h
  have h6 : Entails.eval a c567 := derived567 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c625 := derived625 a h
  have h9 : Entails.eval a c620 := derived620 a h
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c626 := derived626 a h
  have h12 : Entails.eval a c323 := h 322 (by decide)
  have h13 : Entails.eval a c627 := derived627 a h
  have h14 : Entails.eval a c197 := h 196 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c55 := h 54 (by decide)
  have h18 : Entails.eval a c48 := h 47 (by decide)
  have h19 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c606, some c618, some c622, some c624, some c628, some c195, some c185, some c347, some c348, some c28, some c192, some c6, some c201, some c19, some c323, some c175, some c174, some c345, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c559, c606, c618, c622, c624, c628, c195, c185, c347, c348, c28, c192, c6, c201, c19, c323, c175, c174, c345] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c606 := derived606 a h
  have h2 : Entails.eval a c618 := derived618 a h
  have h3 : Entails.eval a c622 := derived622 a h
  have h4 : Entails.eval a c624 := derived624 a h
  have h5 : Entails.eval a c628 := derived628 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c192 := h 191 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c174 := h 173 (by decide)
  have h18 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c618, some c114, some c107, some c328, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c629, c618, c114, c107, c328] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c618 := derived618 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨42, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c629, some c618, some c630, some c119, some c146, some c215, some c141, some c347, some c328, some c185, some c196, some c192, some c178, some c329, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c559, c629, c618, c630, c119, c146, c215, c141, c347, c328, c185, c196, c192, c178, c329] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c618 := derived618 a h
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c328 := h 327 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c192 := h 191 (by decide)
  have h13 : Entails.eval a c178 := h 177 (by decide)
  have h14 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c629, some c631, some c202, some c347, some c328, some c179, some c330, some c344, some c184, some c178, some c196, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c618, c629, c631, c202, c347, c328, c179, c330, c344, c184, c178, c196] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c179 := h 178 (by decide)
  have h7 : Entails.eval a c330 := h 329 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c184 := h 183 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c618, some c631, some c202, some c632, some c189, some c353, some c330, some c361, some c179, some c174, some c339, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c629, c618, c631, c202, c632, c189, c353, c330, c361, c179, c174, c339] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c618 := derived618 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c632 := derived632 a h
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c330 := h 329 (by decide)
  have h8 : Entails.eval a c361 := derived361 a h
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c629, some c559, some c633, some c19, some c188, some c7, some c92, some c88, some c100, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c606, c629, c559, c633, c19, c188, c7, c92, c88, c100] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c633 := derived633 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c629, some c559, some c141, some c114, some c634, some c353, some c189, some c202, some c119, some c146, some c215, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c618, c629, c559, c141, c114, c634, c353, c189, c202, c119, c146, c215] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c634 := derived634 a h
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c19, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c606, c19] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c33, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c559, c33] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c36, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c606, c36] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c57, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c559, c57] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c85, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c559, c85] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c92, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c559, c92] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c106, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c606, c106] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c119, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c559, c119] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c122, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c606, c122] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c133, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c629, c133] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c141, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c629, c141] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c146, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c559, c146] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c158, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c629, c158] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c179, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c629, c179] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c185, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c559, c185] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c188, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c629, c188] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨13, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c189, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c629, c189] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c192, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c559, c192] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c245, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c559, c245] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨34, by decide⟩, false), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c308, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c618, c308] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨34, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c618, some c310, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c618, c310] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c618 := derived618 a h
  have h1 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived656

end CochromaticTwenty.Certificates.B16_5_0
