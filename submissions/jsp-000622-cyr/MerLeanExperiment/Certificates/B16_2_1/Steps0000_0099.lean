import MerLeanExperiment.Certificates.B16_2_1.Inputs

/-! Generated from the actual pinned b16_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c323 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f323 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c303, some c308, some c289, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p323 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked323 : lratChecker f323 p323 = .success := by decide +kernel
theorem unsat323 : Unsatisfiable (PosFin 57) f323 := by
  apply lratCheckerSound f323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p323
  · intro a ha; simp [p323] at ha; subst a; trivial
  · exact checked323
theorem derived323 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c323 := by
  apply localUnsat_implies_entails f323 [c303, c308, c289] c323 unsat323 (by rfl) a
  have h0 : Entails.eval a c303 := h 302 (by decide)
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c324 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f324 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c299, some c302, some c292, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p324 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked324 : lratChecker f324 p324 = .success := by decide +kernel
theorem unsat324 : Unsatisfiable (PosFin 57) f324 := by
  apply lratCheckerSound f324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p324
  · intro a ha; simp [p324] at ha; subst a; trivial
  · exact checked324
theorem derived324 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c324 := by
  apply localUnsat_implies_entails f324 [c299, c302, c292] c324 unsat324 (by rfl) a
  have h0 : Entails.eval a c299 := h 298 (by decide)
  have h1 : Entails.eval a c302 := h 301 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c325 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨40, by decide⟩, false), (⟨44, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f325 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c286, some c279, some c259, some c270, some c120, some c184, some c121, some c185, some c113, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p325 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked325 : lratChecker f325 p325 = .success := by decide +kernel
theorem unsat325 : Unsatisfiable (PosFin 57) f325 := by
  apply lratCheckerSound f325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p325
  · intro a ha; simp [p325] at ha; subst a; trivial
  · exact checked325
theorem derived325 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c325 := by
  apply localUnsat_implies_entails f325 [c286, c279, c259, c270, c120, c184, c121, c185, c113] c325 unsat325 (by rfl) a
  have h0 : Entails.eval a c286 := h 285 (by decide)
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c259 := h 258 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c326 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨32, by decide⟩, true), (⟨37, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f326 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c246, some c249, some c232, some c39, some c271, some c195, some c35, some c233, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p326 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked326 : lratChecker f326 p326 = .success := by decide +kernel
theorem unsat326 : Unsatisfiable (PosFin 57) f326 := by
  apply lratCheckerSound f326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p326
  · intro a ha; simp [p326] at ha; subst a; trivial
  · exact checked326
theorem derived326 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c326 := by
  apply localUnsat_implies_entails f326 [c185, c246, c249, c232, c39, c271, c195, c35, c233] c326 unsat326 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c327 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f327 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c24, some c186, some c210, some c39, some c234, some c181, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p327 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked327 : lratChecker f327 p327 = .success := by decide +kernel
theorem unsat327 : Unsatisfiable (PosFin 57) f327 := by
  apply lratCheckerSound f327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p327
  · intro a ha; simp [p327] at ha; subst a; trivial
  · exact checked327
theorem derived327 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c327 := by
  apply localUnsat_implies_entails f327 [c233, c24, c186, c210, c39, c234, c181] c327 unsat327 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c234 := h 233 (by decide)
  have h6 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c328 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨32, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨45, by decide⟩, true), (⟨43, by decide⟩, true), (⟨1, by decide⟩, false), (⟨46, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f328 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c321, some c62, some c89, some c88, some c326, some c327, some c36, some c232, some c23, some c197, some c237, some c184, some c32, some c47, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p328 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked328 : lratChecker f328 p328 = .success := by decide +kernel
theorem unsat328 : Unsatisfiable (PosFin 57) f328 := by
  apply lratCheckerSound f328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p328
  · intro a ha; simp [p328] at ha; subst a; trivial
  · exact checked328
theorem derived328 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c328 := by
  apply localUnsat_implies_entails f328 [c321, c62, c89, c88, c326, c327, c36, c232, c23, c197, c237, c184, c32, c47] c328 unsat328 (by rfl) a
  have h0 : Entails.eval a c321 := h 320 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c88 := h 87 (by decide)
  have h4 : Entails.eval a c326 := derived326 a h
  have h5 : Entails.eval a c327 := derived327 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c329 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, true), (⟨45, by decide⟩, true), (⟨3, by decide⟩, false), (⟨41, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f329 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c232, some c23, some c185, some c207, some c45, some c235, some c183, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p329 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked329 : lratChecker f329 p329 = .success := by decide +kernel
theorem unsat329 : Unsatisfiable (PosFin 57) f329 := by
  apply lratCheckerSound f329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p329
  · intro a ha; simp [p329] at ha; subst a; trivial
  · exact checked329
theorem derived329 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c329 := by
  apply localUnsat_implies_entails f329 [c232, c23, c185, c207, c45, c235, c183] c329 unsat329 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c185 := h 184 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c330 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨37, by decide⟩, true), (⟨36, by decide⟩, true), (⟨41, by decide⟩, true), (⟨47, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f330 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c289, some c322, some c321, some c305, some c292, some c306, some c60, some c62, some c89, some c88, some c323, some c276, some c287, some c328, some c288, some c329, some c36, some c233, some c24, some c186, some c200, some c202, some c239, some c182, some c29, some c43, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p330 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked330 : lratChecker f330 p330 = .success := by decide +kernel
theorem unsat330 : Unsatisfiable (PosFin 57) f330 := by
  apply lratCheckerSound f330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p330
  · intro a ha; simp [p330] at ha; subst a; trivial
  · exact checked330
theorem derived330 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c330 := by
  apply localUnsat_implies_entails f330 [c320, c315, c289, c322, c321, c305, c292, c306, c60, c62, c89, c88, c323, c276, c287, c328, c288, c329, c36, c233, c24, c186, c200, c202, c239, c182, c29, c43] c330 unsat330 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c289 := h 288 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c305 := h 304 (by decide)
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c323 := derived323 a h
  have h13 : Entails.eval a c276 := h 275 (by decide)
  have h14 : Entails.eval a c287 := h 286 (by decide)
  have h15 : Entails.eval a c328 := derived328 a h
  have h16 : Entails.eval a c288 := h 287 (by decide)
  have h17 : Entails.eval a c329 := derived329 a h
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c233 := h 232 (by decide)
  have h20 : Entails.eval a c24 := h 23 (by decide)
  have h21 : Entails.eval a c186 := h 185 (by decide)
  have h22 : Entails.eval a c200 := h 199 (by decide)
  have h23 : Entails.eval a c202 := h 201 (by decide)
  have h24 : Entails.eval a c239 := h 238 (by decide)
  have h25 : Entails.eval a c182 := h 181 (by decide)
  have h26 : Entails.eval a c29 := h 28 (by decide)
  have h27 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c331 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨39, by decide⟩, true), (⟨32, by decide⟩, true), (⟨36, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, true), (⟨42, by decide⟩, false), (⟨1, by decide⟩, false), (⟨46, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f331 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c306, some c36, some c233, some c24, some c194, some c210, some c212, some c39, some c271, some c234, some c239, some c248, some c188, some c254, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p331 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked331 : lratChecker f331 p331 = .success := by decide +kernel
theorem unsat331 : Unsatisfiable (PosFin 57) f331 := by
  apply lratCheckerSound f331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p331
  · intro a ha; simp [p331] at ha; subst a; trivial
  · exact checked331
theorem derived331 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c331 := by
  apply localUnsat_implies_entails f331 [c306, c36, c233, c24, c194, c210, c212, c39, c271, c234, c239, c248, c188, c254] c331 unsat331 (by rfl) a
  have h0 : Entails.eval a c306 := h 305 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c234 := h 233 (by decide)
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c188 := h 187 (by decide)
  have h13 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c332 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f332 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c321, some c322, some c324, some c289, some c305, some c292, some c306, some c60, some c62, some c89, some c88, some c323, some c279, some c286, some c325, some c330, some c331, some c232, some c203, some c212, some c233, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p332 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked332 : lratChecker f332 p332 = .success := by decide +kernel
theorem unsat332 : Unsatisfiable (PosFin 57) f332 := by
  apply lratCheckerSound f332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p332
  · intro a ha; simp [p332] at ha; subst a; trivial
  · exact checked332
theorem derived332 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c332 := by
  apply localUnsat_implies_entails f332 [c320, c315, c321, c322, c324, c289, c305, c292, c306, c60, c62, c89, c88, c323, c279, c286, c325, c330, c331, c232, c203, c212, c233] c332 unsat332 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c324 := derived324 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c323 := derived323 a h
  have h14 : Entails.eval a c279 := h 278 (by decide)
  have h15 : Entails.eval a c286 := h 285 (by decide)
  have h16 : Entails.eval a c325 := derived325 a h
  have h17 : Entails.eval a c330 := derived330 a h
  have h18 : Entails.eval a c331 := derived331 a h
  have h19 : Entails.eval a c232 := h 231 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c212 := h 211 (by decide)
  have h22 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c333 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨39, by decide⟩, true), (⟨45, by decide⟩, true), (⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f333 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c232, some c23, some c207, some c212, some c237, some c233, some c32, some c201, some c203, some c58, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p333 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked333 : lratChecker f333 p333 = .success := by decide +kernel
theorem unsat333 : Unsatisfiable (PosFin 57) f333 := by
  apply lratCheckerSound f333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p333
  · intro a ha; simp [p333] at ha; subst a; trivial
  · exact checked333
theorem derived333 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c333 := by
  apply localUnsat_implies_entails f333 [c232, c23, c207, c212, c237, c233, c32, c201, c203, c58] c333 unsat333 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c334 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨46, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f334 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c289, some c322, some c321, some c292, some c306, some c60, some c62, some c89, some c88, some c333, some c205, some c233, some c24, some c204, some c210, some c212, some c51, some c234, some c239, some c196, some c29, some c55, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p334 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked334 : lratChecker f334 p334 = .success := by decide +kernel
theorem unsat334 : Unsatisfiable (PosFin 57) f334 := by
  apply lratCheckerSound f334 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p334
  · intro a ha; simp [p334] at ha; subst a; trivial
  · exact checked334
theorem derived334 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c334 := by
  apply localUnsat_implies_entails f334 [c320, c315, c289, c322, c321, c292, c306, c60, c62, c89, c88, c333, c205, c233, c24, c204, c210, c212, c51, c234, c239, c196, c29, c55] c334 unsat334 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c289 := h 288 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c333 := derived333 a h
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c233 := h 232 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c212 := h 211 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c239 := h 238 (by decide)
  have h21 : Entails.eval a c196 := h 195 (by decide)
  have h22 : Entails.eval a c29 := h 28 (by decide)
  have h23 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c335 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨38, by decide⟩, true), (⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f335 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c204, some c233, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p335 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked335 : lratChecker f335 p335 = .success := by decide +kernel
theorem unsat335 : Unsatisfiable (PosFin 57) f335 := by
  apply lratCheckerSound f335 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p335
  · intro a ha; simp [p335] at ha; subst a; trivial
  · exact checked335
theorem derived335 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c335 := by
  apply localUnsat_implies_entails f335 [c36, c204, c233] c335 unsat335 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c336 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f336 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c58, some c199, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p336 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked336 : lratChecker f336 p336 = .success := by decide +kernel
theorem unsat336 : Unsatisfiable (PosFin 57) f336 := by
  apply lratCheckerSound f336 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p336
  · intro a ha; simp [p336] at ha; subst a; trivial
  · exact checked336
theorem derived336 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c336 := by
  apply localUnsat_implies_entails f336 [c56, c58, c199] c336 unsat336 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c337 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f337 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c321, some c320, some c315, some c323, some c324, some c60, some c289, some c305, some c62, some c292, some c88, some c89, some c306, some c332, some c334, some c287, some c335, some c232, some c23, some c207, some c212, some c93, some c235, some c237, some c233, some c2, some c32, some c150, some c147, some c18, some c162, some c104, some c174, some c336, some c329, some c135, some c288, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p337 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked337 : lratChecker f337 p337 = .success := by decide +kernel
theorem unsat337 : Unsatisfiable (PosFin 57) f337 := by
  apply lratCheckerSound f337 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p337
  · intro a ha; simp [p337] at ha; subst a; trivial
  · exact checked337
theorem derived337 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c337 := by
  apply localUnsat_implies_entails f337 [c322, c321, c320, c315, c323, c324, c60, c289, c305, c62, c292, c88, c89, c306, c332, c334, c287, c335, c232, c23, c207, c212, c93, c235, c237, c233, c2, c32, c150, c147, c18, c162, c104, c174, c336, c329, c135, c288] c337 unsat337 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c323 := derived323 a h
  have h5 : Entails.eval a c324 := derived324 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c292 := h 291 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c332 := derived332 a h
  have h15 : Entails.eval a c334 := derived334 a h
  have h16 : Entails.eval a c287 := h 286 (by decide)
  have h17 : Entails.eval a c335 := derived335 a h
  have h18 : Entails.eval a c232 := h 231 (by decide)
  have h19 : Entails.eval a c23 := h 22 (by decide)
  have h20 : Entails.eval a c207 := h 206 (by decide)
  have h21 : Entails.eval a c212 := h 211 (by decide)
  have h22 : Entails.eval a c93 := h 92 (by decide)
  have h23 : Entails.eval a c235 := h 234 (by decide)
  have h24 : Entails.eval a c237 := h 236 (by decide)
  have h25 : Entails.eval a c233 := h 232 (by decide)
  have h26 : Entails.eval a c2 := h 1 (by decide)
  have h27 : Entails.eval a c32 := h 31 (by decide)
  have h28 : Entails.eval a c150 := h 149 (by decide)
  have h29 : Entails.eval a c147 := h 146 (by decide)
  have h30 : Entails.eval a c18 := h 17 (by decide)
  have h31 : Entails.eval a c162 := h 161 (by decide)
  have h32 : Entails.eval a c104 := h 103 (by decide)
  have h33 : Entails.eval a c174 := h 173 (by decide)
  have h34 : Entails.eval a c336 := derived336 a h
  have h35 : Entails.eval a c329 := derived329 a h
  have h36 : Entails.eval a c135 := h 134 (by decide)
  have h37 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c338 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f338 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c310, some c292, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p338 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked338 : lratChecker f338 p338 = .success := by decide +kernel
theorem unsat338 : Unsatisfiable (PosFin 57) f338 := by
  apply lratCheckerSound f338 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p338
  · intro a ha; simp [p338] at ha; subst a; trivial
  · exact checked338
theorem derived338 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c338 := by
  apply localUnsat_implies_entails f338 [c309, c310, c292] c338 unsat338 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c339 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f339 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c292, some c93, some c307, some c61, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p339 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked339 : lratChecker f339 p339 = .success := by decide +kernel
theorem unsat339 : Unsatisfiable (PosFin 57) f339 := by
  apply lratCheckerSound f339 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p339
  · intro a ha; simp [p339] at ha; subst a; trivial
  · exact checked339
theorem derived339 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c339 := by
  apply localUnsat_implies_entails f339 [c62, c292, c93, c307, c61] c339 unsat339 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c340 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f340 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c321, some c322, some c338, some c337, some c320, some c315, some c232, some c23, some c213, some c233, some c212, some c339, some c300, some c60, some c289, some c207, some c307, some c235, some c237, some c63, some c90, some c91, some c95, some c31, some c2, some c336, some c149, some c146, some c329, some c17, some c162, some c49, some c104, some c180, some c135, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p340 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked340 : lratChecker f340 p340 = .success := by decide +kernel
theorem unsat340 : Unsatisfiable (PosFin 57) f340 := by
  apply lratCheckerSound f340 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p340
  · intro a ha; simp [p340] at ha; subst a; trivial
  · exact checked340
theorem derived340 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c340 := by
  apply localUnsat_implies_entails f340 [c321, c322, c338, c337, c320, c315, c232, c23, c213, c233, c212, c339, c300, c60, c289, c207, c307, c235, c237, c63, c90, c91, c95, c31, c2, c336, c149, c146, c329, c17, c162, c49, c104, c180, c135] c340 unsat340 (by rfl) a
  have h0 : Entails.eval a c321 := h 320 (by decide)
  have h1 : Entails.eval a c322 := h 321 (by decide)
  have h2 : Entails.eval a c338 := derived338 a h
  have h3 : Entails.eval a c337 := derived337 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c232 := h 231 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c339 := derived339 a h
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c235 := h 234 (by decide)
  have h18 : Entails.eval a c237 := h 236 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  have h20 : Entails.eval a c90 := h 89 (by decide)
  have h21 : Entails.eval a c91 := h 90 (by decide)
  have h22 : Entails.eval a c95 := h 94 (by decide)
  have h23 : Entails.eval a c31 := h 30 (by decide)
  have h24 : Entails.eval a c2 := h 1 (by decide)
  have h25 : Entails.eval a c336 := derived336 a h
  have h26 : Entails.eval a c149 := h 148 (by decide)
  have h27 : Entails.eval a c146 := h 145 (by decide)
  have h28 : Entails.eval a c329 := derived329 a h
  have h29 : Entails.eval a c17 := h 16 (by decide)
  have h30 : Entails.eval a c162 := h 161 (by decide)
  have h31 : Entails.eval a c49 := h 48 (by decide)
  have h32 : Entails.eval a c104 := h 103 (by decide)
  have h33 : Entails.eval a c180 := h 179 (by decide)
  have h34 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c341 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨47, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f341 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c338, some c320, some c315, some c23, some c213, some c233, some c212, some c339, some c300, some c60, some c289, some c307, some c63, some c90, some c91, some c35, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p341 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked341 : lratChecker f341 p341 = .success := by decide +kernel
theorem unsat341 : Unsatisfiable (PosFin 57) f341 := by
  apply lratCheckerSound f341 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p341
  · intro a ha; simp [p341] at ha; subst a; trivial
  · exact checked341
theorem derived341 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c341 := by
  apply localUnsat_implies_entails f341 [c338, c320, c315, c23, c213, c233, c212, c339, c300, c60, c289, c307, c63, c90, c91, c35] c341 unsat341 (by rfl) a
  have h0 : Entails.eval a c338 := derived338 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c339 := derived339 a h
  have h8 : Entails.eval a c300 := h 299 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c342 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨18, by decide⟩, true), (⟨42, by decide⟩, false), (⟨43, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f342 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c278, some c198, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p342 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked342 : lratChecker f342 p342 = .success := by decide +kernel
theorem unsat342 : Unsatisfiable (PosFin 57) f342 := by
  apply lratCheckerSound f342 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p342
  · intro a ha; simp [p342] at ha; subst a; trivial
  · exact checked342
theorem derived342 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c342 := by
  apply localUnsat_implies_entails f342 [c274, c278, c198] c342 unsat342 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c343 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨42, by decide⟩, false), (⟨43, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f343 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c257, some c190, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p343 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked343 : lratChecker f343 p343 = .success := by decide +kernel
theorem unsat343 : Unsatisfiable (PosFin 57) f343 := by
  apply lratCheckerSound f343 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p343
  · intro a ha; simp [p343] at ha; subst a; trivial
  · exact checked343
theorem derived343 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c343 := by
  apply localUnsat_implies_entails f343 [c253, c257, c190] c343 unsat343 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c344 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f344 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c190, some c44, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p344 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked344 : lratChecker f344 p344 = .success := by decide +kernel
theorem unsat344 : Unsatisfiable (PosFin 57) f344 := by
  apply lratCheckerSound f344 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p344
  · intro a ha; simp [p344] at ha; subst a; trivial
  · exact checked344
theorem derived344 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c344 := by
  apply localUnsat_implies_entails f344 [c195, c190, c44] c344 unsat344 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c345 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f345 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c300, some c289, some c60, some c321, some c322, some c337, some c340, some c341, some c63, some c90, some c91, some c35, some c233, some c25, some c211, some c88, some c236, some c241, some c3, some c29, some c146, some c159, some c169, some c342, some c343, some c183, some c110, some c344, some c270, some c131, some c40, some c44, some c188, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p345 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked345 : lratChecker f345 p345 = .success := by decide +kernel
theorem unsat345 : Unsatisfiable (PosFin 57) f345 := by
  apply lratCheckerSound f345 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p345
  · intro a ha; simp [p345] at ha; subst a; trivial
  · exact checked345
theorem derived345 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c345 := by
  apply localUnsat_implies_entails f345 [c320, c315, c300, c289, c60, c321, c322, c337, c340, c341, c63, c90, c91, c35, c233, c25, c211, c88, c236, c241, c3, c29, c146, c159, c169, c342, c343, c183, c110, c344, c270, c131, c40, c44, c188] c345 unsat345 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c337 := derived337 a h
  have h8 : Entails.eval a c340 := derived340 a h
  have h9 : Entails.eval a c341 := derived341 a h
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c233 := h 232 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c236 := h 235 (by decide)
  have h19 : Entails.eval a c241 := h 240 (by decide)
  have h20 : Entails.eval a c3 := h 2 (by decide)
  have h21 : Entails.eval a c29 := h 28 (by decide)
  have h22 : Entails.eval a c146 := h 145 (by decide)
  have h23 : Entails.eval a c159 := h 158 (by decide)
  have h24 : Entails.eval a c169 := h 168 (by decide)
  have h25 : Entails.eval a c342 := derived342 a h
  have h26 : Entails.eval a c343 := derived343 a h
  have h27 : Entails.eval a c183 := h 182 (by decide)
  have h28 : Entails.eval a c110 := h 109 (by decide)
  have h29 : Entails.eval a c344 := derived344 a h
  have h30 : Entails.eval a c270 := h 269 (by decide)
  have h31 : Entails.eval a c131 := h 130 (by decide)
  have h32 : Entails.eval a c40 := h 39 (by decide)
  have h33 : Entails.eval a c44 := h 43 (by decide)
  have h34 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c346 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, true), (⟨35, by decide⟩, true), (⟨18, by decide⟩, true), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f346 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c259, some c325, some c247, some c198, some c275, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p346 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked346 : lratChecker f346 p346 = .success := by decide +kernel
theorem unsat346 : Unsatisfiable (PosFin 57) f346 := by
  apply lratCheckerSound f346 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p346
  · intro a ha; simp [p346] at ha; subst a; trivial
  · exact checked346
theorem derived346 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c346 := by
  apply localUnsat_implies_entails f346 [c259, c325, c247, c198, c275] c346 unsat346 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c325 := derived325 a h
  have h2 : Entails.eval a c247 := h 246 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c347 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨43, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f347 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c343, some c119, some c153, some c346, some c123, some c190, some c279, some c254, some c247, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p347 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked347 : lratChecker f347 p347 = .success := by decide +kernel
theorem unsat347 : Unsatisfiable (PosFin 57) f347 := by
  apply lratCheckerSound f347 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p347
  · intro a ha; simp [p347] at ha; subst a; trivial
  · exact checked347
theorem derived347 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c347 := by
  apply localUnsat_implies_entails f347 [c342, c343, c119, c153, c346, c123, c190, c279, c254, c247] c347 unsat347 (by rfl) a
  have h0 : Entails.eval a c342 := derived342 a h
  have h1 : Entails.eval a c343 := derived343 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c346 := derived346 a h
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c348 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨48, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f348 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c278, some c279, some c199, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true))]
def p348 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked348 : lratChecker f348 p348 = .success := by decide +kernel
theorem unsat348 : Unsatisfiable (PosFin 57) f348 := by
  apply lratCheckerSound f348 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p348
  · intro a ha; simp [p348] at ha; subst a; trivial
  · exact checked348
theorem derived348 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c348 := by
  apply localUnsat_implies_entails f348 [c278, c279, c199] c348 unsat348 (by rfl) a
  have h0 : Entails.eval a c278 := h 277 (by decide)
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c349 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f349 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c321, some c322, some c337, some c340, some c341, some c320, some c315, some c300, some c289, some c345, some c347, some c239, some c241, some c348, some c187, some c257, some c259, some c191, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p349 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked349 : lratChecker f349 p349 = .success := by decide +kernel
theorem unsat349 : Unsatisfiable (PosFin 57) f349 := by
  apply lratCheckerSound f349 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p349
  · intro a ha; simp [p349] at ha; subst a; trivial
  · exact checked349
theorem derived349 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c349 := by
  apply localUnsat_implies_entails f349 [c321, c322, c337, c340, c341, c320, c315, c300, c289, c345, c347, c239, c241, c348, c187, c257, c259, c191] c349 unsat349 (by rfl) a
  have h0 : Entails.eval a c321 := h 320 (by decide)
  have h1 : Entails.eval a c322 := h 321 (by decide)
  have h2 : Entails.eval a c337 := derived337 a h
  have h3 : Entails.eval a c340 := derived340 a h
  have h4 : Entails.eval a c341 := derived341 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c345 := derived345 a h
  have h10 : Entails.eval a c347 := derived347 a h
  have h11 : Entails.eval a c239 := h 238 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c348 := derived348 a h
  have h14 : Entails.eval a c187 := h 186 (by decide)
  have h15 : Entails.eval a c257 := h 256 (by decide)
  have h16 : Entails.eval a c259 := h 258 (by decide)
  have h17 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c350 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f350 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c322, some c321, some c320, some c315, some c337, some c338, some c340, some c341, some c349, some c62, some c292, some c302, some c60, some c289, some c88, some c89, some c307, some c25, some c75, some c233, some c93, some c210, some c29, some c239, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p350 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked350 : lratChecker f350 p350 = .success := by decide +kernel
theorem unsat350 : Unsatisfiable (PosFin 57) f350 := by
  apply lratCheckerSound f350 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p350
  · intro a ha; simp [p350] at ha; subst a; trivial
  · exact checked350
theorem derived350 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c350 := by
  apply localUnsat_implies_entails f350 [c322, c321, c320, c315, c337, c338, c340, c341, c349, c62, c292, c302, c60, c289, c88, c89, c307, c25, c75, c233, c93, c210, c29, c239] c350 unsat350 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c337 := derived337 a h
  have h5 : Entails.eval a c338 := derived338 a h
  have h6 : Entails.eval a c340 := derived340 a h
  have h7 : Entails.eval a c341 := derived341 a h
  have h8 : Entails.eval a c349 := derived349 a h
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c292 := h 291 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c289 := h 288 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c307 := h 306 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c233 := h 232 (by decide)
  have h20 : Entails.eval a c93 := h 92 (by decide)
  have h21 : Entails.eval a c210 := h 209 (by decide)
  have h22 : Entails.eval a c29 := h 28 (by decide)
  have h23 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c351 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f351 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c48, some c191, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p351 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked351 : lratChecker f351 p351 = .success := by decide +kernel
theorem unsat351 : Unsatisfiable (PosFin 57) f351 := by
  apply lratCheckerSound f351 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p351
  · intro a ha; simp [p351] at ha; subst a; trivial
  · exact checked351
theorem derived351 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c351 := by
  apply localUnsat_implies_entails f351 [c46, c48, c191] c351 unsat351 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c352 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f352 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c292, some c89, some c1, some c60, some c142, some c4, some c351, some c187, some c57, some c59, some c199, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p352 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked352 : lratChecker f352 p352 = .success := by decide +kernel
theorem unsat352 : Unsatisfiable (PosFin 57) f352 := by
  apply lratCheckerSound f352 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p352
  · intro a ha; simp [p352] at ha; subst a; trivial
  · exact checked352
theorem derived352 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c352 := by
  apply localUnsat_implies_entails f352 [c62, c292, c89, c1, c60, c142, c4, c351, c187, c57, c59, c199] c352 unsat352 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c292 := h 291 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c351 := derived351 a h
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c353 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f353 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c89, some c1, some c60, some c141, some c162, some c142, some c63, some c351, some c187, some c57, some c59, some c199, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p353 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked353 : lratChecker f353 p353 = .success := by decide +kernel
theorem unsat353 : Unsatisfiable (PosFin 57) f353 := by
  apply lratCheckerSound f353 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p353
  · intro a ha; simp [p353] at ha; subst a; trivial
  · exact checked353
theorem derived353 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c353 := by
  apply localUnsat_implies_entails f353 [c352, c89, c1, c60, c141, c162, c142, c63, c351, c187, c57, c59, c199] c353 unsat353 (by rfl) a
  have h0 : Entails.eval a c352 := derived352 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c142 := h 141 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c351 := derived351 a h
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c354 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨49, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f354 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c352, some c353, some c3, some c81, some c91, some c1, some c60, some c141, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p354 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked354 : lratChecker f354 p354 = .success := by decide +kernel
theorem unsat354 : Unsatisfiable (PosFin 57) f354 := by
  apply lratCheckerSound f354 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p354
  · intro a ha; simp [p354] at ha; subst a; trivial
  · exact checked354
theorem derived354 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c354 := by
  apply localUnsat_implies_entails f354 [c352, c353, c3, c81, c91, c1, c60, c141] c354 unsat354 (by rfl) a
  have h0 : Entails.eval a c352 := derived352 a h
  have h1 : Entails.eval a c353 := derived353 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c355 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f355 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c241, some c354, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p355 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked355 : lratChecker f355 p355 = .success := by decide +kernel
theorem unsat355 : Unsatisfiable (PosFin 57) f355 := by
  apply lratCheckerSound f355 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p355
  · intro a ha; simp [p355] at ha; subst a; trivial
  · exact checked355
theorem derived355 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c355 := by
  apply localUnsat_implies_entails f355 [c239, c241, c354] c355 unsat355 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c354 := derived354 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c356 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨42, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f356 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c320, some c315, some c305, some c304, some c215, some c233, some c214, some c307, some c63, some c91, some c99, some c1, some c60, some c78, some c75, some c143, some c141, some c96, some c94, some c13, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p356 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked356 : lratChecker f356 p356 = .success := by decide +kernel
theorem unsat356 : Unsatisfiable (PosFin 57) f356 := by
  apply lratCheckerSound f356 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p356
  · intro a ha; simp [p356] at ha; subst a; trivial
  · exact checked356
theorem derived356 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c356 := by
  apply localUnsat_implies_entails f356 [c26, c320, c315, c305, c304, c215, c233, c214, c307, c63, c91, c99, c1, c60, c78, c75, c143, c141, c96, c94, c13] c356 unsat356 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c214 := h 213 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c143 := h 142 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c94 := h 93 (by decide)
  have h20 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c357 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f357 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c322, some c321, some c320, some c315, some c232, some c26, some c355, some c208, some c356, some c62, some c292, some c98, some c89, some c307, some c306, some c69, some c1, some c78, some c74, some c142, some c96, some c4, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p357 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked357 : lratChecker f357 p357 = .success := by decide +kernel
theorem unsat357 : Unsatisfiable (PosFin 57) f357 := by
  apply lratCheckerSound f357 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p357
  · intro a ha; simp [p357] at ha; subst a; trivial
  · exact checked357
theorem derived357 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c357 := by
  apply localUnsat_implies_entails f357 [c350, c322, c321, c320, c315, c232, c26, c355, c208, c356, c62, c292, c98, c89, c307, c306, c69, c1, c78, c74, c142, c96, c4] c357 unsat357 (by rfl) a
  have h0 : Entails.eval a c350 := derived350 a h
  have h1 : Entails.eval a c322 := h 321 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c355 := derived355 a h
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c356 := derived356 a h
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c306 := h 305 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c1 := h 0 (by decide)
  have h18 : Entails.eval a c78 := h 77 (by decide)
  have h19 : Entails.eval a c74 := h 73 (by decide)
  have h20 : Entails.eval a c142 := h 141 (by decide)
  have h21 : Entails.eval a c96 := h 95 (by decide)
  have h22 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c358 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f358 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c356, some c62, some c292, some c98, some c306, some c23, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p358 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked358 : lratChecker f358 p358 = .success := by decide +kernel
theorem unsat358 : Unsatisfiable (PosFin 57) f358 := by
  apply lratCheckerSound f358 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p358
  · intro a ha; simp [p358] at ha; subst a; trivial
  · exact checked358
theorem derived358 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c358 := by
  apply localUnsat_implies_entails f358 [c26, c356, c62, c292, c98, c306, c23] c358 unsat358 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c356 := derived356 a h
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c292 := h 291 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c359 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f359 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c358, some c289, some c61, some c26, some c62, some c292, some c98, some c94, some c301, some c34, some c214, some c233, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p359 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked359 : lratChecker f359 p359 = .success := by decide +kernel
theorem unsat359 : Unsatisfiable (PosFin 57) f359 := by
  apply lratCheckerSound f359 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p359
  · intro a ha; simp [p359] at ha; subst a; trivial
  · exact checked359
theorem derived359 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c359 := by
  apply localUnsat_implies_entails f359 [c320, c315, c358, c289, c61, c26, c62, c292, c98, c94, c301, c34, c214, c233] c359 unsat359 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c358 := derived358 a h
  have h3 : Entails.eval a c289 := h 288 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c214 := h 213 (by decide)
  have h13 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c360 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f360 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c26, some c358, some c61, some c289, some c359, some c299, some c215, some c233, some c214, some c301, some c63, some c99, some c96, some c33, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p360 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked360 : lratChecker f360 p360 = .success := by decide +kernel
theorem unsat360 : Unsatisfiable (PosFin 57) f360 := by
  apply lratCheckerSound f360 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p360
  · intro a ha; simp [p360] at ha; subst a; trivial
  · exact checked360
theorem derived360 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c360 := by
  apply localUnsat_implies_entails f360 [c320, c315, c26, c358, c61, c289, c359, c299, c215, c233, c214, c301, c63, c99, c96, c33] c360 unsat360 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c358 := derived358 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c359 := derived359 a h
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c215 := h 214 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c361 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f361 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c81, some c141, some c91, some c1, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p361 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked361 : lratChecker f361 p361 = .success := by decide +kernel
theorem unsat361 : Unsatisfiable (PosFin 57) f361 := by
  apply lratCheckerSound f361 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p361
  · intro a ha; simp [p361] at ha; subst a; trivial
  · exact checked361
theorem derived361 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c361 := by
  apply localUnsat_implies_entails f361 [c3, c81, c141, c91, c1] c361 unsat361 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c362 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f362 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c91, some c81, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p362 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked362 : lratChecker f362 p362 = .success := by decide +kernel
theorem unsat362 : Unsatisfiable (PosFin 57) f362 := by
  apply lratCheckerSound f362 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p362
  · intro a ha; simp [p362] at ha; subst a; trivial
  · exact checked362
theorem derived362 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c362 := by
  apply localUnsat_implies_entails f362 [c89, c91, c81] c362 unsat362 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c363 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f363 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c362, some c60, some c62, some c361, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p363 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked363 : lratChecker f363 p363 = .success := by decide +kernel
theorem unsat363 : Unsatisfiable (PosFin 57) f363 := by
  apply lratCheckerSound f363 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p363
  · intro a ha; simp [p363] at ha; subst a; trivial
  · exact checked363
theorem derived363 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c363 := by
  apply localUnsat_implies_entails f363 [c362, c60, c62, c361] c363 unsat363 (by rfl) a
  have h0 : Entails.eval a c362 := derived362 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c361 := derived361 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c364 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f364 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c362, some c1, some c60, some c78, some c363, some c98, some c94, some c34, some c233, some c33, some c96, some c4, some c63, some c142, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p364 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked364 : lratChecker f364 p364 = .success := by decide +kernel
theorem unsat364 : Unsatisfiable (PosFin 57) f364 := by
  apply lratCheckerSound f364 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p364
  · intro a ha; simp [p364] at ha; subst a; trivial
  · exact checked364
theorem derived364 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c364 := by
  apply localUnsat_implies_entails f364 [c320, c315, c362, c1, c60, c78, c363, c98, c94, c34, c233, c33, c96, c4, c63, c142] c364 unsat364 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c362 := derived362 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c363 := derived363 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c233 := h 232 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c63 := h 62 (by decide)
  have h15 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c365 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨21, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f365 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c78, some c93, some c94, some c28, some c34, some c104, some c103, some c18, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p365 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked365 : lratChecker f365 p365 = .success := by decide +kernel
theorem unsat365 : Unsatisfiable (PosFin 57) f365 := by
  apply lratCheckerSound f365 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p365
  · intro a ha; simp [p365] at ha; subst a; trivial
  · exact checked365
theorem derived365 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c365 := by
  apply localUnsat_implies_entails f365 [c1, c78, c93, c94, c28, c34, c104, c103, c18] c365 unsat365 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c366 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f366 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c43, some c188, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p366 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked366 : lratChecker f366 p366 = .success := by decide +kernel
theorem unsat366 : Unsatisfiable (PosFin 57) f366 := by
  apply lratCheckerSound f366 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p366
  · intro a ha; simp [p366] at ha; subst a; trivial
  · exact checked366
theorem derived366 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c366 := by
  apply localUnsat_implies_entails f366 [c39, c43, c188] c366 unsat366 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c367 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨41, by decide⟩, false), (⟨21, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f367 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c360, some c320, some c315, some c365, some c88, some c77, some c323, some c299, some c76, some c292, some c90, some c4, some c142, some c159, some c147, some c177, some c176, some c61, some c93, some c34, some c16, some c233, some c109, some c175, some c210, some c235, some c366, some c122, some c128, some c51, some c37, some c118, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p367 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked367 : lratChecker f367 p367 = .success := by decide +kernel
theorem unsat367 : Unsatisfiable (PosFin 57) f367 := by
  apply lratCheckerSound f367 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p367
  · intro a ha; simp [p367] at ha; subst a; trivial
  · exact checked367
theorem derived367 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c367 := by
  apply localUnsat_implies_entails f367 [c364, c360, c320, c315, c365, c88, c77, c323, c299, c76, c292, c90, c4, c142, c159, c147, c177, c176, c61, c93, c34, c16, c233, c109, c175, c210, c235, c366, c122, c128, c51, c37, c118] c367 unsat367 (by rfl) a
  have h0 : Entails.eval a c364 := derived364 a h
  have h1 : Entails.eval a c360 := derived360 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c365 := derived365 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c323 := derived323 a h
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c292 := h 291 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  have h14 : Entails.eval a c159 := h 158 (by decide)
  have h15 : Entails.eval a c147 := h 146 (by decide)
  have h16 : Entails.eval a c177 := h 176 (by decide)
  have h17 : Entails.eval a c176 := h 175 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c93 := h 92 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c16 := h 15 (by decide)
  have h22 : Entails.eval a c233 := h 232 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c175 := h 174 (by decide)
  have h25 : Entails.eval a c210 := h 209 (by decide)
  have h26 : Entails.eval a c235 := h 234 (by decide)
  have h27 : Entails.eval a c366 := derived366 a h
  have h28 : Entails.eval a c122 := h 121 (by decide)
  have h29 : Entails.eval a c128 := h 127 (by decide)
  have h30 : Entails.eval a c51 := h 50 (by decide)
  have h31 : Entails.eval a c37 := h 36 (by decide)
  have h32 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c368 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f368 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c188, some c270, some c44, some c133, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p368 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked368 : lratChecker f368 p368 = .success := by decide +kernel
theorem unsat368 : Unsatisfiable (PosFin 57) f368 := by
  apply lratCheckerSound f368 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p368
  · intro a ha; simp [p368] at ha; subst a; trivial
  · exact checked368
theorem derived368 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c368 := by
  apply localUnsat_implies_entails f368 [c189, c188, c270, c44, c133] c368 unsat368 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c188 := h 187 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c369 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f369 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c40, some c129, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p369 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked369 : lratChecker f369 p369 = .success := by decide +kernel
theorem unsat369 : Unsatisfiable (PosFin 57) f369 := by
  apply lratCheckerSound f369 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p369
  · intro a ha; simp [p369] at ha; subst a; trivial
  · exact checked369
theorem derived369 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c369 := by
  apply localUnsat_implies_entails f369 [c38, c40, c129] c369 unsat369 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c370 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f370 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c321, some c322, some c357, some c364, some c350, some c360, some c320, some c315, some c367, some c3, some c62, some c81, some c141, some c299, some c1, some c159, some c77, some c90, some c146, some c174, some c175, some c76, some c61, some c301, some c95, some c23, some c33, some c15, some c233, some c108, some c177, some c211, some c237, some c369, some c189, some c118, some c368, some c256, some c273, some c112, some c183, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p370 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41]]
theorem checked370 : lratChecker f370 p370 = .success := by decide +kernel
theorem unsat370 : Unsatisfiable (PosFin 57) f370 := by
  apply lratCheckerSound f370 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p370
  · intro a ha; simp [p370] at ha; subst a; trivial
  · exact checked370
theorem derived370 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c370 := by
  apply localUnsat_implies_entails f370 [c321, c322, c357, c364, c350, c360, c320, c315, c367, c3, c62, c81, c141, c299, c1, c159, c77, c90, c146, c174, c175, c76, c61, c301, c95, c23, c33, c15, c233, c108, c177, c211, c237, c369, c189, c118, c368, c256, c273, c112, c183] c370 unsat370 (by rfl) a
  have h0 : Entails.eval a c321 := h 320 (by decide)
  have h1 : Entails.eval a c322 := h 321 (by decide)
  have h2 : Entails.eval a c357 := derived357 a h
  have h3 : Entails.eval a c364 := derived364 a h
  have h4 : Entails.eval a c350 := derived350 a h
  have h5 : Entails.eval a c360 := derived360 a h
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c367 := derived367 a h
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  have h17 : Entails.eval a c90 := h 89 (by decide)
  have h18 : Entails.eval a c146 := h 145 (by decide)
  have h19 : Entails.eval a c174 := h 173 (by decide)
  have h20 : Entails.eval a c175 := h 174 (by decide)
  have h21 : Entails.eval a c76 := h 75 (by decide)
  have h22 : Entails.eval a c61 := h 60 (by decide)
  have h23 : Entails.eval a c301 := h 300 (by decide)
  have h24 : Entails.eval a c95 := h 94 (by decide)
  have h25 : Entails.eval a c23 := h 22 (by decide)
  have h26 : Entails.eval a c33 := h 32 (by decide)
  have h27 : Entails.eval a c15 := h 14 (by decide)
  have h28 : Entails.eval a c233 := h 232 (by decide)
  have h29 : Entails.eval a c108 := h 107 (by decide)
  have h30 : Entails.eval a c177 := h 176 (by decide)
  have h31 : Entails.eval a c211 := h 210 (by decide)
  have h32 : Entails.eval a c237 := h 236 (by decide)
  have h33 : Entails.eval a c369 := derived369 a h
  have h34 : Entails.eval a c189 := h 188 (by decide)
  have h35 : Entails.eval a c118 := h 117 (by decide)
  have h36 : Entails.eval a c368 := derived368 a h
  have h37 : Entails.eval a c256 := h 255 (by decide)
  have h38 : Entails.eval a c273 := h 272 (by decide)
  have h39 : Entails.eval a c112 := h 111 (by decide)
  have h40 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c371 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨42, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f371 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c306, some c304, some c292, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p371 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked371 : lratChecker f371 p371 = .success := by decide +kernel
theorem unsat371 : Unsatisfiable (PosFin 57) f371 := by
  apply lratCheckerSound f371 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p371
  · intro a ha; simp [p371] at ha; subst a; trivial
  · exact checked371
theorem derived371 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c371 := by
  apply localUnsat_implies_entails f371 [c306, c304, c292] c371 unsat371 (by rfl) a
  have h0 : Entails.eval a c306 := h 305 (by decide)
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c372 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f372 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c95, some c81, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p372 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked372 : lratChecker f372 p372 = .success := by decide +kernel
theorem unsat372 : Unsatisfiable (PosFin 57) f372 := by
  apply lratCheckerSound f372 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p372
  · intro a ha; simp [p372] at ha; subst a; trivial
  · exact checked372
theorem derived372 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c372 := by
  apply localUnsat_implies_entails f372 [c93, c95, c81] c372 unsat372 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c373 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨42, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f373 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c62, some c146, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p373 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked373 : lratChecker f373 p373 = .success := by decide +kernel
theorem unsat373 : Unsatisfiable (PosFin 57) f373 := by
  apply lratCheckerSound f373 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p373
  · intro a ha; simp [p373] at ha; subst a; trivial
  · exact checked373
theorem derived373 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c373 := by
  apply localUnsat_implies_entails f373 [c3, c62, c146] c373 unsat373 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c374 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f374 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c321, some c322, some c350, some c357, some c364, some c370, some c60, some c289, some c371, some c23, some c372, some c2, some c373, some c88, some c77, some c323, some c305, some c76, some c292, some c90, some c147, some c4, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p374 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked374 : lratChecker f374 p374 = .success := by decide +kernel
theorem unsat374 : Unsatisfiable (PosFin 57) f374 := by
  apply lratCheckerSound f374 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p374
  · intro a ha; simp [p374] at ha; subst a; trivial
  · exact checked374
theorem derived374 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c374 := by
  apply localUnsat_implies_entails f374 [c320, c315, c321, c322, c350, c357, c364, c370, c60, c289, c371, c23, c372, c2, c373, c88, c77, c323, c305, c76, c292, c90, c147, c4] c374 unsat374 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c322 := h 321 (by decide)
  have h4 : Entails.eval a c350 := derived350 a h
  have h5 : Entails.eval a c357 := derived357 a h
  have h6 : Entails.eval a c364 := derived364 a h
  have h7 : Entails.eval a c370 := derived370 a h
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c289 := h 288 (by decide)
  have h10 : Entails.eval a c371 := derived371 a h
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c372 := derived372 a h
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c373 := derived373 a h
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  have h17 : Entails.eval a c323 := derived323 a h
  have h18 : Entails.eval a c305 := h 304 (by decide)
  have h19 : Entails.eval a c76 := h 75 (by decide)
  have h20 : Entails.eval a c292 := h 291 (by decide)
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c147 := h 146 (by decide)
  have h23 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c375 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨52, by decide⟩, false), (⟨43, by decide⟩, true), (⟨44, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f375 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c73, some c230, some c231, some c323, some c210, some c29, some c36, some c240, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p375 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked375 : lratChecker f375 p375 = .success := by decide +kernel
theorem unsat375 : Unsatisfiable (PosFin 57) f375 := by
  apply lratCheckerSound f375 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p375
  · intro a ha; simp [p375] at ha; subst a; trivial
  · exact checked375
theorem derived375 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c375 := by
  apply localUnsat_implies_entails f375 [c22, c73, c230, c231, c323, c210, c29, c36, c240] c375 unsat375 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c231 := h 230 (by decide)
  have h4 : Entails.eval a c323 := derived323 a h
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c376 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f376 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c47, some c127, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p376 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked376 : lratChecker f376 p376 = .success := by decide +kernel
theorem unsat376 : Unsatisfiable (PosFin 57) f376 := by
  apply lratCheckerSound f376 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p376
  · intro a ha; simp [p376] at ha; subst a; trivial
  · exact checked376
theorem derived376 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c376 := by
  apply localUnsat_implies_entails f376 [c45, c47, c127] c376 unsat376 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c377 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f377 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c121, some c56, some c58, some c136, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p377 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked377 : lratChecker f377 p377 = .success := by decide +kernel
theorem unsat377 : Unsatisfiable (PosFin 57) f377 := by
  apply lratCheckerSound f377 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p377
  · intro a ha; simp [p377] at ha; subst a; trivial
  · exact checked377
theorem derived377 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c377 := by
  apply localUnsat_implies_entails f377 [c376, c121, c56, c58, c136] c377 unsat377 (by rfl) a
  have h0 : Entails.eval a c376 := derived376 a h
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c378 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f378 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c175, some c170, some c18, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p378 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked378 : lratChecker f378 p378 = .success := by decide +kernel
theorem unsat378 : Unsatisfiable (PosFin 57) f378 := by
  apply lratCheckerSound f378 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p378
  · intro a ha; simp [p378] at ha; subst a; trivial
  · exact checked378
theorem derived378 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c378 := by
  apply localUnsat_implies_entails f378 [c175, c170, c18] c378 unsat378 (by rfl) a
  have h0 : Entails.eval a c175 := h 174 (by decide)
  have h1 : Entails.eval a c170 := h 169 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c379 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f379 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c61, some c2, some c373, some c88, some c89, some c306, some c304, some c371, some c148, some c160, some c5, some c375, some c90, some c378, some c377, some c177, some c172, some c17, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p379 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked379 : lratChecker f379 p379 = .success := by decide +kernel
theorem unsat379 : Unsatisfiable (PosFin 57) f379 := by
  apply lratCheckerSound f379 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p379
  · intro a ha; simp [p379] at ha; subst a; trivial
  · exact checked379
theorem derived379 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c379 := by
  apply localUnsat_implies_entails f379 [c78, c61, c2, c373, c88, c89, c306, c304, c371, c148, c160, c5, c375, c90, c378, c377, c177, c172, c17] c379 unsat379 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c373 := derived373 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c371 := derived371 a h
  have h9 : Entails.eval a c148 := h 147 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c375 := derived375 a h
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c378 := derived378 a h
  have h15 : Entails.eval a c377 := derived377 a h
  have h16 : Entails.eval a c177 := h 176 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c380 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f380 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c176, some c17, some c160, some c172, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p380 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked380 : lratChecker f380 p380 = .success := by decide +kernel
theorem unsat380 : Unsatisfiable (PosFin 57) f380 := by
  apply lratCheckerSound f380 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p380
  · intro a ha; simp [p380] at ha; subst a; trivial
  · exact checked380
theorem derived380 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c380 := by
  apply localUnsat_implies_entails f380 [c177, c176, c17, c160, c172] c380 unsat380 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c381 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f381 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c377, some c378, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p381 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked381 : lratChecker f381 p381 = .success := by decide +kernel
theorem unsat381 : Unsatisfiable (PosFin 57) f381 := by
  apply lratCheckerSound f381 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p381
  · intro a ha; simp [p381] at ha; subst a; trivial
  · exact checked381
theorem derived381 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c381 := by
  apply localUnsat_implies_entails f381 [c160, c377, c378] c381 unsat381 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c377 := derived377 a h
  have h2 : Entails.eval a c378 := derived378 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c382 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f382 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c76, some c323, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p382 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked382 : lratChecker f382 p382 = .success := by decide +kernel
theorem unsat382 : Unsatisfiable (PosFin 57) f382 := by
  apply lratCheckerSound f382 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p382
  · intro a ha; simp [p382] at ha; subst a; trivial
  · exact checked382
theorem derived382 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c382 := by
  apply localUnsat_implies_entails f382 [c77, c76, c323] c382 unsat382 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c323 := derived323 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c383 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f383 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c17, some c178, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p383 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked383 : lratChecker f383 p383 = .success := by decide +kernel
theorem unsat383 : Unsatisfiable (PosFin 57) f383 := by
  apply lratCheckerSound f383 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p383
  · intro a ha; simp [p383] at ha; subst a; trivial
  · exact checked383
theorem derived383 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c383 := by
  apply localUnsat_implies_entails f383 [c18, c17, c178] c383 unsat383 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c384 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨44, by decide⟩, true), (⟨43, by decide⟩, true), (⟨29, by decide⟩, true), (⟨52, by decide⟩, false), (⟨41, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f384 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c230, some c233, some c209, some c25, some c36, some c235, some c244, some c189, some c193, some c251, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p384 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked384 : lratChecker f384 p384 = .success := by decide +kernel
theorem unsat384 : Unsatisfiable (PosFin 57) f384 := by
  apply lratCheckerSound f384 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p384
  · intro a ha; simp [p384] at ha; subst a; trivial
  · exact checked384
theorem derived384 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c384 := by
  apply localUnsat_implies_entails f384 [c230, c233, c209, c25, c36, c235, c244, c189, c193, c251] c384 unsat384 (by rfl) a
  have h0 : Entails.eval a c230 := h 229 (by decide)
  have h1 : Entails.eval a c233 := h 232 (by decide)
  have h2 : Entails.eval a c209 := h 208 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c235 := h 234 (by decide)
  have h6 : Entails.eval a c244 := h 243 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c385 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f385 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c315, some c320, some c379, some c290, some c64, some c78, some c61, some c2, some c373, some c88, some c89, some c90, some c380, some c381, some c174, some c162, some c376, some c382, some c300, some c302, some c383, some c384, some c35, some c24, some c231, some c116, some c209, some c192, some c235, some c250, some c189, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p385 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked385 : lratChecker f385 p385 = .success := by decide +kernel
theorem unsat385 : Unsatisfiable (PosFin 57) f385 := by
  apply lratCheckerSound f385 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p385
  · intro a ha; simp [p385] at ha; subst a; trivial
  · exact checked385
theorem derived385 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c385 := by
  apply localUnsat_implies_entails f385 [c374, c315, c320, c379, c290, c64, c78, c61, c2, c373, c88, c89, c90, c380, c381, c174, c162, c376, c382, c300, c302, c383, c384, c35, c24, c231, c116, c209, c192, c235, c250, c189] c385 unsat385 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c379 := derived379 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c373 := derived373 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c380 := derived380 a h
  have h14 : Entails.eval a c381 := derived381 a h
  have h15 : Entails.eval a c174 := h 173 (by decide)
  have h16 : Entails.eval a c162 := h 161 (by decide)
  have h17 : Entails.eval a c376 := derived376 a h
  have h18 : Entails.eval a c382 := derived382 a h
  have h19 : Entails.eval a c300 := h 299 (by decide)
  have h20 : Entails.eval a c302 := h 301 (by decide)
  have h21 : Entails.eval a c383 := derived383 a h
  have h22 : Entails.eval a c384 := derived384 a h
  have h23 : Entails.eval a c35 := h 34 (by decide)
  have h24 : Entails.eval a c24 := h 23 (by decide)
  have h25 : Entails.eval a c231 := h 230 (by decide)
  have h26 : Entails.eval a c116 := h 115 (by decide)
  have h27 : Entails.eval a c209 := h 208 (by decide)
  have h28 : Entails.eval a c192 := h 191 (by decide)
  have h29 : Entails.eval a c235 := h 234 (by decide)
  have h30 : Entails.eval a c250 := h 249 (by decide)
  have h31 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c386 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨4, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f386 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c61, some c2, some c373, some c88, some c89, some c300, some c302, some c292, some c375, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p386 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked386 : lratChecker f386 p386 = .success := by decide +kernel
theorem unsat386 : Unsatisfiable (PosFin 57) f386 := by
  apply lratCheckerSound f386 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p386
  · intro a ha; simp [p386] at ha; subst a; trivial
  · exact checked386
theorem derived386 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c386 := by
  apply localUnsat_implies_entails f386 [c78, c61, c2, c373, c88, c89, c300, c302, c292, c375] c386 unsat386 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c373 := derived373 a h
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c375 := derived375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c387 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f387 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c320, some c315, some c2, some c78, some c61, some c373, some c89, some c88, some c379, some c290, some c385, some c386, some c77, some c150, some c18, some c14, some c172, some c180, some c160, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p387 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked387 : lratChecker f387 p387 = .success := by decide +kernel
theorem unsat387 : Unsatisfiable (PosFin 57) f387 := by
  apply lratCheckerSound f387 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p387
  · intro a ha; simp [p387] at ha; subst a; trivial
  · exact checked387
theorem derived387 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c387 := by
  apply localUnsat_implies_entails f387 [c374, c320, c315, c2, c78, c61, c373, c89, c88, c379, c290, c385, c386, c77, c150, c18, c14, c172, c180, c160] c387 unsat387 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c373 := derived373 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c379 := derived379 a h
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c385 := derived385 a h
  have h12 : Entails.eval a c386 := derived386 a h
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  have h18 : Entails.eval a c180 := h 179 (by decide)
  have h19 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c388 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨47, by decide⟩, false), (⟨41, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f388 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c176, some c180, some c159, some c18, some c144, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p388 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked388 : lratChecker f388 p388 = .success := by decide +kernel
theorem unsat388 : Unsatisfiable (PosFin 57) f388 := by
  apply lratCheckerSound f388 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p388
  · intro a ha; simp [p388] at ha; subst a; trivial
  · exact checked388
theorem derived388 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c388 := by
  apply localUnsat_implies_entails f388 [c176, c180, c159, c18, c144] c388 unsat388 (by rfl) a
  have h0 : Entails.eval a c176 := h 175 (by decide)
  have h1 : Entails.eval a c180 := h 179 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c389 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨41, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f389 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c374, some c320, some c315, some c26, some c77, some c382, some c323, some c299, some c62, some c93, some c5, some c64, some c79, some c388, some c4, some c14, some c231, some c144, some c22, some c32, some c159, some c233, some c109, some c210, some c235, some c244, some c366, some c186, some c192, some c285, some c258, some c184, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p389 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked389 : lratChecker f389 p389 = .success := by decide +kernel
theorem unsat389 : Unsatisfiable (PosFin 57) f389 := by
  apply lratCheckerSound f389 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p389
  · intro a ha; simp [p389] at ha; subst a; trivial
  · exact checked389
theorem derived389 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c389 := by
  apply localUnsat_implies_entails f389 [c387, c374, c320, c315, c26, c77, c382, c323, c299, c62, c93, c5, c64, c79, c388, c4, c14, c231, c144, c22, c32, c159, c233, c109, c210, c235, c244, c366, c186, c192, c285, c258, c184] c389 unsat389 (by rfl) a
  have h0 : Entails.eval a c387 := derived387 a h
  have h1 : Entails.eval a c374 := derived374 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c382 := derived382 a h
  have h7 : Entails.eval a c323 := derived323 a h
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c388 := derived388 a h
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c231 := h 230 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c32 := h 31 (by decide)
  have h21 : Entails.eval a c159 := h 158 (by decide)
  have h22 : Entails.eval a c233 := h 232 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c210 := h 209 (by decide)
  have h25 : Entails.eval a c235 := h 234 (by decide)
  have h26 : Entails.eval a c244 := h 243 (by decide)
  have h27 : Entails.eval a c366 := derived366 a h
  have h28 : Entails.eval a c186 := h 185 (by decide)
  have h29 : Entails.eval a c192 := h 191 (by decide)
  have h30 : Entails.eval a c285 := h 284 (by decide)
  have h31 : Entails.eval a c258 := h 257 (by decide)
  have h32 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c390 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f390 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c374, some c320, some c315, some c389, some c300, some c302, some c62, some c63, some c22, some c73, some c93, some c230, some c231, some c323, some c5, some c79, some c210, some c36, some c35, some c388, some c240, some c234, some c366, some c186, some c194, some c285, some c269, some c120, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p390 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked390 : lratChecker f390 p390 = .success := by decide +kernel
theorem unsat390 : Unsatisfiable (PosFin 57) f390 := by
  apply lratCheckerSound f390 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p390
  · intro a ha; simp [p390] at ha; subst a; trivial
  · exact checked390
theorem derived390 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c390 := by
  apply localUnsat_implies_entails f390 [c387, c374, c320, c315, c389, c300, c302, c62, c63, c22, c73, c93, c230, c231, c323, c5, c79, c210, c36, c35, c388, c240, c234, c366, c186, c194, c285, c269, c120] c390 unsat390 (by rfl) a
  have h0 : Entails.eval a c387 := derived387 a h
  have h1 : Entails.eval a c374 := derived374 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c389 := derived389 a h
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  have h13 : Entails.eval a c231 := h 230 (by decide)
  have h14 : Entails.eval a c323 := derived323 a h
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c79 := h 78 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c388 := derived388 a h
  have h21 : Entails.eval a c240 := h 239 (by decide)
  have h22 : Entails.eval a c234 := h 233 (by decide)
  have h23 : Entails.eval a c366 := derived366 a h
  have h24 : Entails.eval a c186 := h 185 (by decide)
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c285 := h 284 (by decide)
  have h27 : Entails.eval a c269 := h 268 (by decide)
  have h28 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c391 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f391 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c374, some c320, some c315, some c390, some c60, some c289, some c290, some c306, some c371, some c304, some c22, some c73, some c230, some c231, some c323, some c210, some c36, some c35, some c240, some c234, some c366, some c186, some c51, some c55, some c196, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p391 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked391 : lratChecker f391 p391 = .success := by decide +kernel
theorem unsat391 : Unsatisfiable (PosFin 57) f391 := by
  apply lratCheckerSound f391 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p391
  · intro a ha; simp [p391] at ha; subst a; trivial
  · exact checked391
theorem derived391 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c391 := by
  apply localUnsat_implies_entails f391 [c387, c374, c320, c315, c390, c60, c289, c290, c306, c371, c304, c22, c73, c230, c231, c323, c210, c36, c35, c240, c234, c366, c186, c51, c55, c196] c391 unsat391 (by rfl) a
  have h0 : Entails.eval a c387 := derived387 a h
  have h1 : Entails.eval a c374 := derived374 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c390 := derived390 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c371 := derived371 a h
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c231 := h 230 (by decide)
  have h15 : Entails.eval a c323 := derived323 a h
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c240 := h 239 (by decide)
  have h20 : Entails.eval a c234 := h 233 (by decide)
  have h21 : Entails.eval a c366 := derived366 a h
  have h22 : Entails.eval a c186 := h 185 (by decide)
  have h23 : Entails.eval a c51 := h 50 (by decide)
  have h24 : Entails.eval a c55 := h 54 (by decide)
  have h25 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c392 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f392 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c289, some c290, some c304, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p392 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked392 : lratChecker f392 p392 = .success := by decide +kernel
theorem unsat392 : Unsatisfiable (PosFin 57) f392 := by
  apply lratCheckerSound f392 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p392
  · intro a ha; simp [p392] at ha; subst a; trivial
  · exact checked392
theorem derived392 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c392 := by
  apply localUnsat_implies_entails f392 [c289, c290, c304] c392 unsat392 (by rfl) a
  have h0 : Entails.eval a c289 := h 288 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c393 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f393 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c62, some c392, some c141, some c159, some c160, some c174, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p393 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked393 : lratChecker f393 p393 = .success := by decide +kernel
theorem unsat393 : Unsatisfiable (PosFin 57) f393 := by
  apply lratCheckerSound f393 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p393
  · intro a ha; simp [p393] at ha; subst a; trivial
  · exact checked393
theorem derived393 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c393 := by
  apply localUnsat_implies_entails f393 [c3, c62, c392, c141, c159, c160, c174] c393 unsat393 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c392 := derived392 a h
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c159 := h 158 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c394 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f394 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c320, some c315, some c387, some c393, some c93, some c94, some c5, some c64, some c79, some c89, some c391, some c90, some c382, some c157, some c18, some c17, some c383, some c173, some c159, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p394 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked394 : lratChecker f394 p394 = .success := by decide +kernel
theorem unsat394 : Unsatisfiable (PosFin 57) f394 := by
  apply lratCheckerSound f394 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p394
  · intro a ha; simp [p394] at ha; subst a; trivial
  · exact checked394
theorem derived394 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c394 := by
  apply localUnsat_implies_entails f394 [c374, c320, c315, c387, c393, c93, c94, c5, c64, c79, c89, c391, c90, c382, c157, c18, c17, c383, c173, c159] c394 unsat394 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c387 := derived387 a h
  have h4 : Entails.eval a c393 := derived393 a h
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c391 := derived391 a h
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c382 := derived382 a h
  have h14 : Entails.eval a c157 := h 156 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c17 := h 16 (by decide)
  have h17 : Entails.eval a c383 := derived383 a h
  have h18 : Entails.eval a c173 := h 172 (by decide)
  have h19 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c395 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f395 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c157, some c18, some c17, some c173, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p395 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked395 : lratChecker f395 p395 = .success := by decide +kernel
theorem unsat395 : Unsatisfiable (PosFin 57) f395 := by
  apply lratCheckerSound f395 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p395
  · intro a ha; simp [p395] at ha; subst a; trivial
  · exact checked395
theorem derived395 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c395 := by
  apply localUnsat_implies_entails f395 [c382, c157, c18, c17, c173] c395 unsat395 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c157 := h 156 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c396 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨45, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c394, some c320, some c315, some c309, some c310, some c63, some c22, some c73, some c230, some c231, some c323, some c210, some c36, some c227, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p396 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 57) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c394, c320, c315, c309, c310, c63, c22, c73, c230, c231, c323, c210, c36, c227] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c394 := derived394 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c230 := h 229 (by decide)
  have h9 : Entails.eval a c231 := h 230 (by decide)
  have h10 : Entails.eval a c323 := derived323 a h
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c32, some c245, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p397 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 57) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c34, c32, c245] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c64, some c394, some c320, some c315, some c396, some c26, some c77, some c228, some c323, some c397, some c233, some c210, some c392, some c299, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p398 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 57) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c374, c64, c394, c320, c315, c396, c26, c77, c228, c323, c397, c233, c210, c392, c299] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c396 := derived396 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c323 := derived323 a h
  have h10 : Entails.eval a c397 := derived397 a h
  have h11 : Entails.eval a c233 := h 232 (by decide)
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c392 := derived392 a h
  have h14 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c320, some c315, some c5, some c64, some c79, some c89, some c398, some c90, some c382, some c395, some c157, some c159, some c383, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p399 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 57) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c374, c320, c315, c5, c64, c79, c89, c398, c90, c382, c395, c157, c159, c383] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c398 := derived398 a h
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c382 := derived382 a h
  have h10 : Entails.eval a c395 := derived395 a h
  have h11 : Entails.eval a c157 := h 156 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c383 := derived383 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c58, some c136, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p400 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 57) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c56, c58, c136] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c58 := h 57 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c93, some c90, some c380, some c383, some c381, some c179, some c376, some c400, some c185, some c116, some c107, some c29, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p401 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 57) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c98, c93, c90, c380, c383, c381, c179, c376, c400, c185, c116, c107, c29] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c90 := h 89 (by decide)
  have h3 : Entails.eval a c380 := derived380 a h
  have h4 : Entails.eval a c383 := derived383 a h
  have h5 : Entails.eval a c381 := derived381 a h
  have h6 : Entails.eval a c179 := h 178 (by decide)
  have h7 : Entails.eval a c376 := derived376 a h
  have h8 : Entails.eval a c400 := derived400 a h
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c320, some c315, some c396, some c290, some c300, some c302, some c63, some c375, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p402 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 57) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c374, c320, c315, c396, c290, c300, c302, c63, c375] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c396 := derived396 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c375 := derived375 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c394, some c374, some c320, some c315, some c399, some c93, some c98, some c2, some c78, some c61, some c401, some c402, some c26, some c77, some c228, some c323, some c150, some c305, some c210, some c18, some c14, some c233, some c115, some c32, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p403 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 57) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c394, c374, c320, c315, c399, c93, c98, c2, c78, c61, c401, c402, c26, c77, c228, c323, c150, c305, c210, c18, c14, c233, c115, c32] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c394 := derived394 a h
  have h1 : Entails.eval a c374 := derived374 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c399 := derived399 a h
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c401 := derived401 a h
  have h11 : Entails.eval a c402 := derived402 a h
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c77 := h 76 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c323 := derived323 a h
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c305 := h 304 (by decide)
  have h18 : Entails.eval a c210 := h 209 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c233 := h 232 (by decide)
  have h22 : Entails.eval a c115 := h 114 (by decide)
  have h23 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c315, some c403, some c94, some c88, some c78, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p404 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 57) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c320, c315, c403, c94, c88, c78] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c403 := derived403 a h
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c13, some c171, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p405 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 57) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c12, c13, c171] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c79, some c60, some c78, some c95, some c97, some c405, some c141, some c71, some c72, some c301, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p406 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 57) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c1, c79, c60, c78, c95, c97, c405, c141, c71, c72, c301] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c405 := derived405 a h
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c72, some c301, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p407 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 57) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c71, c72, c301] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c301 := h 300 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c141, some c159, some c160, some c174, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p408 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 57) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c141, c159, c160, c174] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c13, some c405, some c177, some c159, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p409 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 57) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c12, c13, c405, c177, c159] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c405 := derived405 a h
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c410 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c409, some c407, some c408, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p410 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 57) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c409, c407, c408] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c408 := derived408 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨6, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c410, some c289, some c290, some c392, some c306, some c71, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p411 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 57) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c410, c289, c290, c392, c306, c71] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c410 := derived410 a h
  have h1 : Entails.eval a c289 := h 288 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c392 := derived392 a h
  have h4 : Entails.eval a c306 := h 305 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c320, some c404, some c315, some c406, some c92, some c411, some c95, some c64, some c5, some c91, some c394, some c289, some c392, some c148, some c306, some c21, some c72, some c159, some c227, some c228, some c308, some c211, some c26, some c35, some c236, some c242, some c157, some c344, some c17, some c260, some c267, some c173, some c171, some c369, some c189, some c188, some c110, some c42, some c127, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p412 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 57) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c374, c320, c404, c315, c406, c92, c411, c95, c64, c5, c91, c394, c289, c392, c148, c306, c21, c72, c159, c227, c228, c308, c211, c26, c35, c236, c242, c157, c344, c17, c260, c267, c173, c171, c369, c189, c188, c110, c42, c127] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c374 := derived374 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c404 := derived404 a h
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c406 := derived406 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c411 := derived411 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c394 := derived394 a h
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c392 := derived392 a h
  have h14 : Entails.eval a c148 := h 147 (by decide)
  have h15 : Entails.eval a c306 := h 305 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c227 := h 226 (by decide)
  have h20 : Entails.eval a c228 := h 227 (by decide)
  have h21 : Entails.eval a c308 := h 307 (by decide)
  have h22 : Entails.eval a c211 := h 210 (by decide)
  have h23 : Entails.eval a c26 := h 25 (by decide)
  have h24 : Entails.eval a c35 := h 34 (by decide)
  have h25 : Entails.eval a c236 := h 235 (by decide)
  have h26 : Entails.eval a c242 := h 241 (by decide)
  have h27 : Entails.eval a c157 := h 156 (by decide)
  have h28 : Entails.eval a c344 := derived344 a h
  have h29 : Entails.eval a c17 := h 16 (by decide)
  have h30 : Entails.eval a c260 := h 259 (by decide)
  have h31 : Entails.eval a c267 := h 266 (by decide)
  have h32 : Entails.eval a c173 := h 172 (by decide)
  have h33 : Entails.eval a c171 := h 170 (by decide)
  have h34 : Entails.eval a c369 := derived369 a h
  have h35 : Entails.eval a c189 := h 188 (by decide)
  have h36 : Entails.eval a c188 := h 187 (by decide)
  have h37 : Entails.eval a c110 := h 109 (by decide)
  have h38 : Entails.eval a c42 := h 41 (by decide)
  have h39 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c413 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c412, some c374, some c320, some c404, some c315, some c406, some c92, some c411, some c95, some c64, some c5, some c91, some c394, some c21, some c72, some c227, some c228, some c303, some c301, some c211, some c26, some c35, some c236, some c242, some c157, some c344, some c17, some c252, some c260, some c267, some c114, some c189, some c188, some c110, some c42, some c127, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p413 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 57) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c412, c374, c320, c404, c315, c406, c92, c411, c95, c64, c5, c91, c394, c21, c72, c227, c228, c303, c301, c211, c26, c35, c236, c242, c157, c344, c17, c252, c260, c267, c114, c189, c188, c110, c42, c127] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c412 := derived412 a h
  have h1 : Entails.eval a c374 := derived374 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c404 := derived404 a h
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c406 := derived406 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c411 := derived411 a h
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c394 := derived394 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c211 := h 210 (by decide)
  have h20 : Entails.eval a c26 := h 25 (by decide)
  have h21 : Entails.eval a c35 := h 34 (by decide)
  have h22 : Entails.eval a c236 := h 235 (by decide)
  have h23 : Entails.eval a c242 := h 241 (by decide)
  have h24 : Entails.eval a c157 := h 156 (by decide)
  have h25 : Entails.eval a c344 := derived344 a h
  have h26 : Entails.eval a c17 := h 16 (by decide)
  have h27 : Entails.eval a c252 := h 251 (by decide)
  have h28 : Entails.eval a c260 := h 259 (by decide)
  have h29 : Entails.eval a c267 := h 266 (by decide)
  have h30 : Entails.eval a c114 := h 113 (by decide)
  have h31 : Entails.eval a c189 := h 188 (by decide)
  have h32 : Entails.eval a c188 := h 187 (by decide)
  have h33 : Entails.eval a c110 := h 109 (by decide)
  have h34 : Entails.eval a c42 := h 41 (by decide)
  have h35 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c320, some c374, some c404, some c406, some c92, some c411, some c91, some c394, some c412, some c413, some c300, some c299, some c408, some c26, some c76, some c13, some c228, some c301, some c143, some c31, some c159, some c233, some c108, some c380, some c178, some c211, some c369, some c237, some c245, some c118, some c188, some c189, some c273, some c272, some c119, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p414 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 57) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c315, c320, c374, c404, c406, c92, c411, c91, c394, c412, c413, c300, c299, c408, c26, c76, c13, c228, c301, c143, c31, c159, c233, c108, c380, c178, c211, c369, c237, c245, c118, c188, c189, c273, c272, c119] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c374 := derived374 a h
  have h3 : Entails.eval a c404 := derived404 a h
  have h4 : Entails.eval a c406 := derived406 a h
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c411 := derived411 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c394 := derived394 a h
  have h9 : Entails.eval a c412 := derived412 a h
  have h10 : Entails.eval a c413 := derived413 a h
  have h11 : Entails.eval a c300 := h 299 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c408 := derived408 a h
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c228 := h 227 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c143 := h 142 (by decide)
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c159 := h 158 (by decide)
  have h22 : Entails.eval a c233 := h 232 (by decide)
  have h23 : Entails.eval a c108 := h 107 (by decide)
  have h24 : Entails.eval a c380 := derived380 a h
  have h25 : Entails.eval a c178 := h 177 (by decide)
  have h26 : Entails.eval a c211 := h 210 (by decide)
  have h27 : Entails.eval a c369 := derived369 a h
  have h28 : Entails.eval a c237 := h 236 (by decide)
  have h29 : Entails.eval a c245 := h 244 (by decide)
  have h30 : Entails.eval a c118 := h 117 (by decide)
  have h31 : Entails.eval a c188 := h 187 (by decide)
  have h32 : Entails.eval a c189 := h 188 (by decide)
  have h33 : Entails.eval a c273 := h 272 (by decide)
  have h34 : Entails.eval a c272 := h 271 (by decide)
  have h35 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨10, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c408, some c76, some c13, some c149, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p415 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 57) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c300, c408, c76, c13, c149] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c408 := derived408 a h
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c414, some c61, some c2, some c315, some c374, some c404, some c406, some c92, some c411, some c91, some c394, some c415, some c21, some c72, some c227, some c228, some c303, some c301, some c211, some c29, some c35, some c242, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p416 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 57) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c320, c414, c61, c2, c315, c374, c404, c406, c92, c411, c91, c394, c415, c21, c72, c227, c228, c303, c301, c211, c29, c35, c242] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c374 := derived374 a h
  have h6 : Entails.eval a c404 := derived404 a h
  have h7 : Entails.eval a c406 := derived406 a h
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c411 := derived411 a h
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c394 := derived394 a h
  have h12 : Entails.eval a c415 := derived415 a h
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c227 := h 226 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c211 := h 210 (by decide)
  have h20 : Entails.eval a c29 := h 28 (by decide)
  have h21 : Entails.eval a c35 := h 34 (by decide)
  have h22 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c404, some c394, some c374, some c320, some c315, some c406, some c92, some c411, some c91, some c414, some c61, some c416, some c290, some c392, some c306, some c21, some c72, some c227, some c228, some c308, some c211, some c29, some c35, some c242, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p417 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 57) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c404, c394, c374, c320, c315, c406, c92, c411, c91, c414, c61, c416, c290, c392, c306, c21, c72, c227, c228, c308, c211, c29, c35, c242] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c404 := derived404 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c374 := derived374 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c406 := derived406 a h
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c411 := derived411 a h
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c414 := derived414 a h
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c416 := derived416 a h
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c392 := derived392 a h
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c72 := h 71 (by decide)
  have h17 : Entails.eval a c227 := h 226 (by decide)
  have h18 : Entails.eval a c228 := h 227 (by decide)
  have h19 : Entails.eval a c308 := h 307 (by decide)
  have h20 : Entails.eval a c211 := h 210 (by decide)
  have h21 : Entails.eval a c29 := h 28 (by decide)
  have h22 : Entails.eval a c35 := h 34 (by decide)
  have h23 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c417, some c404, some c394, some c374, some c320, some c315, some c60, some c289, some c290, some c392, some c306, some c21, some c71, some c227, some c228, some c91, some c36, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p418 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 57) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c417, c404, c394, c374, c320, c315, c60, c289, c290, c392, c306, c21, c71, c227, c228, c91, c36] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c417 := derived417 a h
  have h1 : Entails.eval a c404 := derived404 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c374 := derived374 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c289 := h 288 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c392 := derived392 a h
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c227 := h 226 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c91 := h 90 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c91, some c99, some c79, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p419 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 57) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c91, c99, c79] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c91 := h 90 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c418, some c417, some c404, some c394, some c374, some c320, some c315, some c21, some c227, some c228, some c25, some c36, some c323, some c419, some c71, some c32, some c302, some c214, some c242, some c230, some c4, some c142, some c159, some c208, some c147, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p420 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 57) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c418, c417, c404, c394, c374, c320, c315, c21, c227, c228, c25, c36, c323, c419, c71, c32, c302, c214, c242, c230, c4, c142, c159, c208, c147] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c418 := derived418 a h
  have h1 : Entails.eval a c417 := derived417 a h
  have h2 : Entails.eval a c404 := derived404 a h
  have h3 : Entails.eval a c394 := derived394 a h
  have h4 : Entails.eval a c374 := derived374 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c323 := derived323 a h
  have h13 : Entails.eval a c419 := derived419 a h
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c302 := h 301 (by decide)
  have h17 : Entails.eval a c214 := h 213 (by decide)
  have h18 : Entails.eval a c242 := h 241 (by decide)
  have h19 : Entails.eval a c230 := h 229 (by decide)
  have h20 : Entails.eval a c4 := h 3 (by decide)
  have h21 : Entails.eval a c142 := h 141 (by decide)
  have h22 : Entails.eval a c159 := h 158 (by decide)
  have h23 : Entails.eval a c208 := h 207 (by decide)
  have h24 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c320, some c374, some c404, some c417, some c418, some c420, some c300, some c299, some c408, some c77, some c419, some c73, some c12, some c142, some c159, some c160, some c176, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p421 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 57) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c315, c320, c374, c404, c417, c418, c420, c300, c299, c408, c77, c419, c73, c12, c142, c159, c160, c176] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c374 := derived374 a h
  have h3 : Entails.eval a c404 := derived404 a h
  have h4 : Entails.eval a c417 := derived417 a h
  have h5 : Entails.eval a c418 := derived418 a h
  have h6 : Entails.eval a c420 := derived420 a h
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c408 := derived408 a h
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c419 := derived419 a h
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c142 := h 141 (by decide)
  have h15 : Entails.eval a c159 := h 158 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c142, some c154, some c160, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p422 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 57) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c142, c154, c160] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c142 := h 141 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived422

end CochromaticTwenty.Certificates.B16_2_1
