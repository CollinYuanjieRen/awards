import MerLeanExperiment.Certificates.B16_7_1.Steps0100_0199

/-! Generated from the actual pinned b16_7_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c558 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨27, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c542, some c347, some c508, some c356, some c37, some c76, some c555, some c556, some c75, some c409, some c557, some c183, some c184, some c134, some c170, some c291, some c354, some c490, some c285, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c542, c347, c508, c356, c37, c76, c555, c556, c75, c409, c557, c183, c184, c134, c170, c291, c354, c490, c285] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c542 := derived542 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c555 := derived555 a h
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c409 := derived409 a h
  have h10 : Entails.eval a c557 := derived557 a h
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c490 := derived490 a h
  have h18 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c180, some c172, some c181, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c180, c172, c181] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c180 := h 179 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c356, some c542, some c76, some c37, some c508, some c555, some c559, some c558, some c290, some c556, some c532, some c47, some c96, some c289, some c129, some c184, some c286, some c75, some c171, some c354, some c40, some c291, some c102, some c229, some c189, some c233, some c35, some c107, some c109, some c261, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c347, c356, c542, c76, c37, c508, c555, c559, c558, c290, c556, c532, c47, c96, c289, c129, c184, c286, c75, c171, c354, c40, c291, c102, c229, c189, c233, c35, c107, c109, c261] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c542 := derived542 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c555 := derived555 a h
  have h7 : Entails.eval a c559 := derived559 a h
  have h8 : Entails.eval a c558 := derived558 a h
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c556 := derived556 a h
  have h11 : Entails.eval a c532 := derived532 a h
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c129 := h 128 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c286 := h 285 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c171 := h 170 (by decide)
  have h20 : Entails.eval a c354 := h 353 (by decide)
  have h21 : Entails.eval a c40 := h 39 (by decide)
  have h22 : Entails.eval a c291 := h 290 (by decide)
  have h23 : Entails.eval a c102 := h 101 (by decide)
  have h24 : Entails.eval a c229 := h 228 (by decide)
  have h25 : Entails.eval a c189 := h 188 (by decide)
  have h26 : Entails.eval a c233 := h 232 (by decide)
  have h27 : Entails.eval a c35 := h 34 (by decide)
  have h28 : Entails.eval a c107 := h 106 (by decide)
  have h29 : Entails.eval a c109 := h 108 (by decide)
  have h30 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c347, some c356, some c542, some c37, some c76, some c555, some c556, some c75, some c559, some c558, some c290, some c289, some c532, some c129, some c47, some c184, some c560, some c182, some c17, some c519, some c126, some c139, some c291, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c508, c347, c356, c542, c37, c76, c555, c556, c75, c559, c558, c290, c289, c532, c129, c47, c184, c560, c182, c17, c519, c126, c139, c291] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c347 := h 346 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c542 := derived542 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c555 := derived555 a h
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c559 := derived559 a h
  have h10 : Entails.eval a c558 := derived558 a h
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c532 := derived532 a h
  have h14 : Entails.eval a c129 := h 128 (by decide)
  have h15 : Entails.eval a c47 := h 46 (by decide)
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c560 := derived560 a h
  have h18 : Entails.eval a c182 := h 181 (by decide)
  have h19 : Entails.eval a c17 := h 16 (by decide)
  have h20 : Entails.eval a c519 := derived519 a h
  have h21 : Entails.eval a c126 := h 125 (by decide)
  have h22 : Entails.eval a c139 := h 138 (by decide)
  have h23 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c139, some c354, some c186, some c168, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c169, c139, c354, c186, c168] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c562, some c184, some c18, some c133, some c42, some c186, some c354, some c168, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c562, c184, c18, c133, c42, c186, c354, c168] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c562 := derived562 a h
  have h1 : Entails.eval a c184 := h 183 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c186 := h 185 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c508, some c290, some c289, some c532, some c43, some c129, some c563, some c291, some c284, some c354, some c169, some c184, some c98, some c133, some c227, some c186, some c100, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c561, c125, c508, c290, c289, c532, c43, c129, c563, c291, c284, c354, c169, c184, c98, c133, c227, c186, c100] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c290 := h 289 (by decide)
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c532 := derived532 a h
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c563 := derived563 a h
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c184 := h 183 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c227 := h 226 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  have h18 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨52, by decide⟩, true), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c508, some c463, some c295, some c286, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c561, c508, c463, c295, c286] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c463 := derived463 a h
  have h3 : Entails.eval a c295 := h 294 (by decide)
  have h4 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c508, some c2, some c78, some c80, some c85, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c561, c508, c2, c78, c80, c85] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c168, some c186, some c182, some c565, some c131, some c133, some c299, some c41, some c566, some c45, some c14, some c90, some c78, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c561, c125, c168, c186, c182, c565, c131, c133, c299, c41, c566, c45, c14, c90, c78] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c565 := derived565 a h
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c41 := h 40 (by decide)
  have h10 : Entails.eval a c566 := derived566 a h
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c508, some c564, some c567, some c349, some c354, some c123, some c37, some c280, some c169, some c509, some c299, some c3, some c81, some c79, some c86, some c90, some c47, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c561, c125, c508, c564, c567, c349, c354, c123, c37, c280, c169, c509, c299, c3, c81, c79, c86, c90, c47] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c564 := derived564 a h
  have h4 : Entails.eval a c567 := derived567 a h
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c280 := h 279 (by decide)
  have h10 : Entails.eval a c169 := h 168 (by decide)
  have h11 : Entails.eval a c509 := derived509 a h
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c79 := h 78 (by decide)
  have h16 : Entails.eval a c86 := h 85 (by decide)
  have h17 : Entails.eval a c90 := h 89 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c568, some c508, some c567, some c349, some c123, some c37, some c280, some c279, some c509, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c568, c508, c567, c349, c123, c37, c280, c279, c509] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c568 := derived568 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c280 := h 279 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c509 := derived509 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c508, some c568, some c569, some c289, some c532, some c129, some c124, some c38, some c522, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c561, c125, c508, c568, c569, c289, c532, c129, c124, c38, c522] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c568 := derived568 a h
  have h4 : Entails.eval a c569 := derived569 a h
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c532 := derived532 a h
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨25, by decide⟩, false), (⟨26, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c38, some c522, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c124, c38, c522] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c571, some c561, some c125, some c289, some c43, some c522, some c91, some c94, some c133, some c79, some c354, some c168, some c284, some c78, some c291, some c16, some c53, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c508, c571, c561, c125, c289, c43, c522, c91, c94, c133, c79, c354, c168, c284, c78, c291, c16, c53] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c571 := derived571 a h
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c522 := derived522 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c168 := h 167 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c16 := h 15 (by decide)
  have h17 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, false), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c225, some c31, some c105, some c107, some c251, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c561, c125, c225, c31, c105, c107, c251] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c225 := h 224 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨10, by decide⟩, true), (⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c570, some c127, some c294, some c299, some c133, some c98, some c508, some c172, some c572, some c47, some c289, some c168, some c284, some c178, some c16, some c291, some c166, some c78, some c573, some c195, some c196, some c248, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c561, c125, c570, c127, c294, c299, c133, c98, c508, c172, c572, c47, c289, c168, c284, c178, c16, c291, c166, c78, c573, c195, c196, c248] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c570 := derived570 a h
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c508 := derived508 a h
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c572 := derived572 a h
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c284 := h 283 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c16 := h 15 (by decide)
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c166 := h 165 (by decide)
  have h19 : Entails.eval a c78 := h 77 (by decide)
  have h20 : Entails.eval a c573 := derived573 a h
  have h21 : Entails.eval a c195 := h 194 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  have h23 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨50, by decide⟩, false), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c172, some c349, some c354, some c166, some c171, some c179, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c508, c172, c349, c354, c166, c171, c179] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c349 := h 348 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c570, some c127, some c299, some c294, some c508, some c172, some c289, some c571, some c572, some c47, some c575, some c168, some c284, some c574, some c291, some c184, some c169, some c139, some c102, some c178, some c16, some c229, some c166, some c78, some c189, some c573, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c561, c125, c570, c127, c299, c294, c508, c172, c289, c571, c572, c47, c575, c168, c284, c574, c291, c184, c169, c139, c102, c178, c16, c229, c166, c78, c189, c573] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c570 := derived570 a h
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c299 := h 298 (by decide)
  have h5 : Entails.eval a c294 := h 293 (by decide)
  have h6 : Entails.eval a c508 := derived508 a h
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c571 := derived571 a h
  have h10 : Entails.eval a c572 := derived572 a h
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c575 := derived575 a h
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c284 := h 283 (by decide)
  have h15 : Entails.eval a c574 := derived574 a h
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c169 := h 168 (by decide)
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c102 := h 101 (by decide)
  have h21 : Entails.eval a c178 := h 177 (by decide)
  have h22 : Entails.eval a c16 := h 15 (by decide)
  have h23 : Entails.eval a c229 := h 228 (by decide)
  have h24 : Entails.eval a c166 := h 165 (by decide)
  have h25 : Entails.eval a c78 := h 77 (by decide)
  have h26 : Entails.eval a c189 := h 188 (by decide)
  have h27 : Entails.eval a c573 := derived573 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c123, some c131, some c97, some c184, some c225, some c169, some c189, some c223, some c117, some c119, some c244, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c561, c123, c131, c97, c184, c225, c169, c189, c223, c117, c119, c244] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨15, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c125, some c299, some c294, some c508, some c168, some c178, some c566, some c133, some c497, some c45, some c80, some c10, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c561, c125, c299, c294, c508, c168, c178, c566, c133, c497, c45, c80, c10] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c508 := derived508 a h
  have h5 : Entails.eval a c168 := h 167 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c566 := derived566 a h
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c497 := derived497 a h
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c508, some c125, some c570, some c127, some c172, some c294, some c299, some c576, some c577, some c179, some c169, some c578, some c349, some c354, some c279, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c561, c508, c125, c570, c127, c172, c294, c299, c576, c577, c179, c169, c578, c349, c354, c279] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c570 := derived570 a h
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c576 := derived576 a h
  have h9 : Entails.eval a c577 := derived577 a h
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c169 := h 168 (by decide)
  have h12 : Entails.eval a c578 := derived578 a h
  have h13 : Entails.eval a c349 := h 348 (by decide)
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c579, some c559, some c561, some c127, some c172, some c175, some c123, some c131, some c349, some c463, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c508, c579, c559, c561, c127, c172, c175, c123, c131, c349, c463] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c559 := derived559 a h
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c175 := h 174 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c463 := derived463 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c580, some c508, some c579, some c559, some c561, some c123, some c131, some c349, some c565, some c463, some c39, some c41, some c11, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c580, c508, c579, c559, c561, c123, c131, c349, c565, c463, c39, c41, c11] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c580 := derived580 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c579 := derived579 a h
  have h3 : Entails.eval a c559 := derived559 a h
  have h4 : Entails.eval a c561 := derived561 a h
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c131 := h 130 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c565 := derived565 a h
  have h9 : Entails.eval a c463 := derived463 a h
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨9, by decide⟩, false), (⟨13, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c175, some c129, some c561, some c295, some c39, some c1, some c11, some c37, some c46, some c349, some c463, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c508, c175, c129, c561, c295, c39, c1, c11, c37, c46, c349, c463] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c175 := h 174 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c295 := h 294 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c349 := h 348 (by decide)
  have h11 : Entails.eval a c463 := derived463 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨32, by decide⟩, false), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c299, some c300, some c39, some c282, some c1, some c349, some c37, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c561, c299, c300, c39, c282, c1, c349, c37] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c579, some c561, some c508, some c580, some c581, some c175, some c582, some c517, some c583, some c280, some c41, some c349, some c11, some c170, some c78, some c14, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c579, c561, c508, c580, c581, c175, c582, c517, c583, c280, c41, c349, c11, c170, c78, c14] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c579 := derived579 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c580 := derived580 a h
  have h4 : Entails.eval a c581 := derived581 a h
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c582 := derived582 a h
  have h7 : Entails.eval a c517 := derived517 a h
  have h8 : Entails.eval a c583 := derived583 a h
  have h9 : Entails.eval a c280 := h 279 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨13, by decide⟩, false), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c584, some c579, some c561, some c508, some c290, some c369, some c39, some c349, some c11, some c82, some c76, some c85, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c584, c579, c561, c508, c290, c369, c39, c349, c11, c82, c76, c85] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c584 := derived584 a h
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c369 := derived369 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c584, some c579, some c561, some c508, some c585, some c517, some c532, some c39, some c11, some c82, some c41, some c85, some c463, some c76, some c349, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c584, c579, c561, c508, c585, c517, c532, c39, c11, c82, c41, c85, c463, c76, c349] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c584 := derived584 a h
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c585 := derived585 a h
  have h5 : Entails.eval a c517 := derived517 a h
  have h6 : Entails.eval a c532 := derived532 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c463 := derived463 a h
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c559, some c133, some c13, some c12, some c47, some c82, some c90, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c559, c133, c13, c12, c47, c82, c90] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c559 := derived559 a h
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c96, some c47, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c92, c96, c47] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c171, some c79, some c18, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c171, c79, c18] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c171 := h 170 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c584, some c508, some c586, some c579, some c172, some c175, some c166, some c349, some c561, some c369, some c127, some c463, some c587, some c39, some c289, some c284, some c291, some c559, some c98, some c124, some c43, some c589, some c229, some c195, some c133, some c451, some c456, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c584, c508, c586, c579, c172, c175, c166, c349, c561, c369, c127, c463, c587, c39, c289, c284, c291, c559, c98, c124, c43, c589, c229, c195, c133, c451, c456] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c584 := derived584 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c586 := derived586 a h
  have h3 : Entails.eval a c579 := derived579 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c561 := derived561 a h
  have h9 : Entails.eval a c369 := derived369 a h
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c463 := derived463 a h
  have h12 : Entails.eval a c587 := derived587 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c291 := h 290 (by decide)
  have h17 : Entails.eval a c559 := derived559 a h
  have h18 : Entails.eval a c98 := h 97 (by decide)
  have h19 : Entails.eval a c124 := h 123 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c589 := derived589 a h
  have h22 : Entails.eval a c229 := h 228 (by decide)
  have h23 : Entails.eval a c195 := h 194 (by decide)
  have h24 : Entails.eval a c133 := h 132 (by decide)
  have h25 : Entails.eval a c451 := derived451 a h
  have h26 : Entails.eval a c456 := derived456 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c508, some c579, some c559, some c584, some c586, some c127, some c172, some c175, some c166, some c349, some c369, some c463, some c98, some c124, some c587, some c39, some c289, some c43, some c284, some c291, some c589, some c229, some c102, some c18, some c590, some c53, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c561, c508, c579, c559, c584, c586, c127, c172, c175, c166, c349, c369, c463, c98, c124, c587, c39, c289, c43, c284, c291, c589, c229, c102, c18, c590, c53] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c508 := derived508 a h
  have h2 : Entails.eval a c579 := derived579 a h
  have h3 : Entails.eval a c559 := derived559 a h
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c586 := derived586 a h
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c172 := h 171 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c166 := h 165 (by decide)
  have h10 : Entails.eval a c349 := h 348 (by decide)
  have h11 : Entails.eval a c369 := derived369 a h
  have h12 : Entails.eval a c463 := derived463 a h
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c587 := derived587 a h
  have h16 : Entails.eval a c39 := h 38 (by decide)
  have h17 : Entails.eval a c289 := h 288 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c291 := h 290 (by decide)
  have h21 : Entails.eval a c589 := derived589 a h
  have h22 : Entails.eval a c229 := h 228 (by decide)
  have h23 : Entails.eval a c102 := h 101 (by decide)
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c590 := derived590 a h
  have h26 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨11, by decide⟩, false), (⟨32, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c517, some c591, some c357, some c561, some c78, some c588, some c39, some c508, some c289, some c129, some c181, some c98, some c124, some c133, some c228, some c101, some c109, some c319, some c261, some c57, some c268, some c273, some c161, some c71, some c62, some c88, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c517, c591, c357, c561, c78, c588, c39, c508, c289, c129, c181, c98, c124, c133, c228, c101, c109, c319, c261, c57, c268, c273, c161, c71, c62, c88] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c517 := derived517 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c561 := derived561 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c588 := derived588 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c508 := derived508 a h
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c181 := h 180 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c101 := h 100 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c319 := h 318 (by decide)
  have h18 : Entails.eval a c261 := h 260 (by decide)
  have h19 : Entails.eval a c57 := h 56 (by decide)
  have h20 : Entails.eval a c268 := h 267 (by decide)
  have h21 : Entails.eval a c273 := h 272 (by decide)
  have h22 : Entails.eval a c161 := h 160 (by decide)
  have h23 : Entails.eval a c71 := h 70 (by decide)
  have h24 : Entails.eval a c62 := h 61 (by decide)
  have h25 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c175, some c181, some c131, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c175, c181, c131] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c175 := h 174 (by decide)
  have h1 : Entails.eval a c181 := h 180 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c78, some c39, some c88, some c46, some c16, some c497, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c591, c357, c561, c78, c39, c88, c46, c16, c497] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c497 := derived497 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨32, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c78, some c588, some c508, some c592, some c593, some c170, some c594, some c47, some c7, some c133, some c131, some c176, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c591, c357, c561, c78, c588, c508, c592, c593, c170, c594, c47, c7, c133, c131, c176] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c588 := derived588 a h
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c593 := derived593 a h
  have h8 : Entails.eval a c170 := h 169 (by decide)
  have h9 : Entails.eval a c594 := derived594 a h
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c131 := h 130 (by decide)
  have h14 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c595, some c168, some c78, some c588, some c594, some c47, some c7, some c133, some c131, some c178, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c561, c591, c357, c595, c168, c78, c588, c594, c47, c7, c133, c131, c178] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c588 := derived588 a h
  have h7 : Entails.eval a c594 := derived594 a h
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c78, some c39, some c508, some c595, some c168, some c596, some c289, some c129, some c284, some c572, some c291, some c47, some c16, some c133, some c139, some c184, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c591, c357, c561, c78, c39, c508, c595, c168, c596, c289, c129, c284, c572, c291, c47, c16, c133, c139, c184] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c595 := derived595 a h
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c596 := derived596 a h
  have h9 : Entails.eval a c289 := h 288 (by decide)
  have h10 : Entails.eval a c129 := h 128 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c572 := derived572 a h
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c133 := h 132 (by decide)
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c88, some c46, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c96, c88, c46] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c508, some c168, some c170, some c593, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c591, c357, c561, c508, c168, c170, c593] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c168 := h 167 (by decide)
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c593 := derived593 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c131, some c132, some c182, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c131, c132, c182] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c131 := h 130 (by decide)
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c39, some c78, some c597, some c290, some c299, some c599, some c600, some c2, some c45, some c46, some c92, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c591, c357, c561, c39, c78, c597, c290, c299, c599, c600, c2, c45, c46, c92] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c597 := derived597 a h
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c599 := derived599 a h
  have h9 : Entails.eval a c600 := derived600 a h
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c46 := h 45 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c599, some c601, some c591, some c357, some c600, some c566, some c45, some c46, some c90, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c599, c601, c591, c357, c600, c566, c45, c46, c90] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c601 := derived601 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c600 := derived600 a h
  have h5 : Entails.eval a c566 := derived566 a h
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c369, some c602, some c299, some c300, some c282, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c591, c357, c561, c369, c602, c299, c300, c282] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c369 := derived369 a h
  have h4 : Entails.eval a c602 := derived602 a h
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c131, some c176, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c133, c131, c176] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨3, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c47, some c86, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c45, c47, c86] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c603, some c601, some c591, some c357, some c508, some c599, some c605, some c91, some c80, some c7, some c133, some c131, some c178, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c603, c601, c591, c357, c508, c599, c605, c91, c80, c7, c133, c131, c178] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c601 := derived601 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c508 := derived508 a h
  have h5 : Entails.eval a c599 := derived599 a h
  have h6 : Entails.eval a c605 := derived605 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c606, some c603, some c601, some c591, some c357, some c561, some c508, some c91, some c43, some c80, some c289, some c293, some c93, some c125, some c53, some c6, some c13, some c133, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c606, c603, c601, c591, c357, c561, c508, c91, c43, c80, c289, c293, c93, c125, c53, c6, c13, c133] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c606 := derived606 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c601 := derived601 a h
  have h3 : Entails.eval a c591 := derived591 a h
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c561 := derived561 a h
  have h6 : Entails.eval a c508 := derived508 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c125 := h 124 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c607, some c38, some c603, some c47, some c606, some c601, some c591, some c357, some c561, some c98, some c133, some c228, some c13, some c125, some c168, some c289, some c186, some c101, some c109, some c261, some c107, some c245, some c31, some c196, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c607, c38, c603, c47, c606, c601, c591, c357, c561, c98, c133, c228, c13, c125, c168, c289, c186, c101, c109, c261, c107, c245, c31, c196] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c607 := derived607 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c603 := derived603 a h
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c606 := derived606 a h
  have h5 : Entails.eval a c601 := derived601 a h
  have h6 : Entails.eval a c591 := derived591 a h
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c561 := derived561 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c125 := h 124 (by decide)
  have h14 : Entails.eval a c168 := h 167 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  have h16 : Entails.eval a c186 := h 185 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c261 := h 260 (by decide)
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c31 := h 30 (by decide)
  have h23 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c607, some c38, some c603, some c47, some c606, some c601, some c591, some c357, some c561, some c508, some c13, some c125, some c168, some c289, some c186, some c183, some c284, some c169, some c291, some c137, some c102, some c229, some c189, some c237, some c31, some c109, some c107, some c261, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c608, c607, c38, c603, c47, c606, c601, c591, c357, c561, c508, c13, c125, c168, c289, c186, c183, c284, c169, c291, c137, c102, c229, c189, c237, c31, c109, c107, c261] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c607 := derived607 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c603 := derived603 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c606 := derived606 a h
  have h6 : Entails.eval a c601 := derived601 a h
  have h7 : Entails.eval a c591 := derived591 a h
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c561 := derived561 a h
  have h10 : Entails.eval a c508 := derived508 a h
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c284 := h 283 (by decide)
  have h18 : Entails.eval a c169 := h 168 (by decide)
  have h19 : Entails.eval a c291 := h 290 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c102 := h 101 (by decide)
  have h22 : Entails.eval a c229 := h 228 (by decide)
  have h23 : Entails.eval a c189 := h 188 (by decide)
  have h24 : Entails.eval a c237 := h 236 (by decide)
  have h25 : Entails.eval a c31 := h 30 (by decide)
  have h26 : Entails.eval a c109 := h 108 (by decide)
  have h27 : Entails.eval a c107 := h 106 (by decide)
  have h28 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c609, some c608, some c606, some c603, some c591, some c357, some c561, some c508, some c125, some c168, some c289, some c183, some c284, some c139, some c291, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c609, c608, c606, c603, c591, c357, c561, c508, c125, c168, c289, c183, c284, c139, c291] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c609 := derived609 a h
  have h1 : Entails.eval a c608 := derived608 a h
  have h2 : Entails.eval a c606 := derived606 a h
  have h3 : Entails.eval a c603 := derived603 a h
  have h4 : Entails.eval a c591 := derived591 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c561 := derived561 a h
  have h7 : Entails.eval a c508 := derived508 a h
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c508, some c603, some c606, some c608, some c609, some c610, some c181, some c129, some c170, some c293, some c183, some c139, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c591, c357, c508, c603, c606, c608, c609, c610, c181, c129, c170, c293, c183, c139] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c508 := derived508 a h
  have h3 : Entails.eval a c603 := derived603 a h
  have h4 : Entails.eval a c606 := derived606 a h
  have h5 : Entails.eval a c608 := derived608 a h
  have h6 : Entails.eval a c609 := derived609 a h
  have h7 : Entails.eval a c610 := derived610 a h
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c180, some c182, some c168, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c591, c357, c561, c180, c182, c168] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c612, some c561, some c591, some c357, some c611, some c463, some c508, some c125, some c168, some c295, some c183, some c284, some c137, some c291, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c612, c561, c591, c357, c611, c463, c508, c125, c168, c295, c183, c284, c137, c291] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c612 := derived612 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c463 := derived463 a h
  have h6 : Entails.eval a c508 := derived508 a h
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c137 := h 136 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c508, some c612, some c613, some c181, some c129, some c170, some c293, some c183, some c137, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c561, c591, c357, c611, c463, c508, c612, c613, c181, c129, c170, c293, c183, c137] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c612 := derived612 a h
  have h7 : Entails.eval a c613 := derived613 a h
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c449, some c104, some c508, some c289, some c293, some c39, some c137, some c195, some c13, some c53, some c15, some c80, some c12, some c85, some c91, some c36, some c111, some c254, some c260, some c63, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c561, c591, c357, c611, c463, c449, c104, c508, c289, c293, c39, c137, c195, c13, c53, c15, c80, c12, c85, c91, c36, c111, c254, c260, c63] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c449 := derived449 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c508 := derived508 a h
  have h8 : Entails.eval a c289 := h 288 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c85 := h 84 (by decide)
  have h19 : Entails.eval a c91 := h 90 (by decide)
  have h20 : Entails.eval a c36 := h 35 (by decide)
  have h21 : Entails.eval a c111 := h 110 (by decide)
  have h22 : Entails.eval a c254 := h 253 (by decide)
  have h23 : Entails.eval a c260 := h 259 (by decide)
  have h24 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c508, some c449, some c104, some c615, some c43, some c129, some c284, some c12, some c291, some c78, some c137, some c16, some c15, some c53, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c561, c591, c357, c611, c463, c508, c449, c104, c615, c43, c129, c284, c12, c291, c78, c137, c16, c15, c53] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c449 := derived449 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c615 := derived615 a h
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c129 := h 128 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c137 := h 136 (by decide)
  have h16 : Entails.eval a c16 := h 15 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c616, some c185, some c561, some c591, some c357, some c611, some c463, some c508, some c43, some c129, some c284, some c12, some c291, some c78, some c139, some c15, some c14, some c51, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c616, c185, c561, c591, c357, c611, c463, c508, c43, c129, c284, c12, c291, c78, c139, c15, c14, c51] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c616 := derived616 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c591 := derived591 a h
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c463 := derived463 a h
  have h7 : Entails.eval a c508 := derived508 a h
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c508, some c616, some c185, some c104, some c237, some c617, some c289, some c293, some c39, some c139, some c193, some c11, some c51, some c15, some c80, some c12, some c85, some c91, some c36, some c111, some c254, some c260, some c63, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c561, c591, c357, c611, c463, c508, c616, c185, c104, c237, c617, c289, c293, c39, c139, c193, c11, c51, c15, c80, c12, c85, c91, c36, c111, c254, c260, c63] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c616 := derived616 a h
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c237 := h 236 (by decide)
  have h10 : Entails.eval a c617 := derived617 a h
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c293 := h 292 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c193 := h 192 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c80 := h 79 (by decide)
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c85 := h 84 (by decide)
  have h22 : Entails.eval a c91 := h 90 (by decide)
  have h23 : Entails.eval a c36 := h 35 (by decide)
  have h24 : Entails.eval a c111 := h 110 (by decide)
  have h25 : Entails.eval a c254 := h 253 (by decide)
  have h26 : Entails.eval a c260 := h 259 (by decide)
  have h27 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c126, some c291, some c508, some c170, some c561, some c611, some c463, some c11, some c12, some c51, some c80, some c93, some c87, some c33, some c108, some c252, some c257, some c63, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c591, c357, c126, c291, c508, c170, c561, c611, c463, c11, c12, c51, c80, c93, c87, c33, c108, c252, c257, c63] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c126 := h 125 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c508 := derived508 a h
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c561 := derived561 a h
  have h7 : Entails.eval a c611 := derived611 a h
  have h8 : Entails.eval a c463 := derived463 a h
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c257 := h 256 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c591, some c357, some c618, some c170, some c175, some c126, some c291, some c614, some c561, some c611, some c463, some c185, some c104, some c237, some c193, some c619, some c39, some c441, some c243, some c248, some c113, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c508, c591, c357, c618, c170, c175, c126, c291, c614, c561, c611, c463, c185, c104, c237, c193, c619, c39, c441, c243, c248, c113] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c618 := derived618 a h
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c614 := derived614 a h
  have h9 : Entails.eval a c561 := derived561 a h
  have h10 : Entails.eval a c611 := derived611 a h
  have h11 : Entails.eval a c463 := derived463 a h
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c237 := h 236 (by decide)
  have h15 : Entails.eval a c193 := h 192 (by decide)
  have h16 : Entails.eval a c619 := derived619 a h
  have h17 : Entails.eval a c39 := h 38 (by decide)
  have h18 : Entails.eval a c441 := derived441 a h
  have h19 : Entails.eval a c243 := h 242 (by decide)
  have h20 : Entails.eval a c248 := h 247 (by decide)
  have h21 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c243, some c248, some c113, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c243, c248, c113] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c243 := h 242 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c614, some c561, some c591, some c357, some c611, some c463, some c508, some c618, some c126, some c170, some c291, some c175, some c620, some c449, some c104, some c195, some c621, some c196, some c289, some c39, some c13, some c12, some c53, some c80, some c93, some c87, some c33, some c108, some c252, some c257, some c63, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c614, c561, c591, c357, c611, c463, c508, c618, c126, c170, c291, c175, c620, c449, c104, c195, c621, c196, c289, c39, c13, c12, c53, c80, c93, c87, c33, c108, c252, c257, c63] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c614 := derived614 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c463 := derived463 a h
  have h6 : Entails.eval a c508 := derived508 a h
  have h7 : Entails.eval a c618 := derived618 a h
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c291 := h 290 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c620 := derived620 a h
  have h13 : Entails.eval a c449 := derived449 a h
  have h14 : Entails.eval a c104 := h 103 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c621 := derived621 a h
  have h17 : Entails.eval a c196 := h 195 (by decide)
  have h18 : Entails.eval a c289 := h 288 (by decide)
  have h19 : Entails.eval a c39 := h 38 (by decide)
  have h20 : Entails.eval a c13 := h 12 (by decide)
  have h21 : Entails.eval a c12 := h 11 (by decide)
  have h22 : Entails.eval a c53 := h 52 (by decide)
  have h23 : Entails.eval a c80 := h 79 (by decide)
  have h24 : Entails.eval a c93 := h 92 (by decide)
  have h25 : Entails.eval a c87 := h 86 (by decide)
  have h26 : Entails.eval a c33 := h 32 (by decide)
  have h27 : Entails.eval a c108 := h 107 (by decide)
  have h28 : Entails.eval a c252 := h 251 (by decide)
  have h29 : Entails.eval a c257 := h 256 (by decide)
  have h30 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨22, by decide⟩, false), (⟨31, by decide⟩, true), (⟨12, by decide⟩, false), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c196, some c178, some c621, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c104, c196, c178, c621] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c621 := derived621 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c591, some c357, some c611, some c561, some c622, some c125, some c295, some c284, some c291, some c168, some c614, some c463, some c623, some c237, some c449, some c194, some c186, some c621, some c139, some c177, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c508, c591, c357, c611, c561, c622, c125, c295, c284, c291, c168, c614, c463, c623, c237, c449, c194, c186, c621, c139, c177] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c561 := derived561 a h
  have h5 : Entails.eval a c622 := derived622 a h
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c614 := derived614 a h
  have h12 : Entails.eval a c463 := derived463 a h
  have h13 : Entails.eval a c623 := derived623 a h
  have h14 : Entails.eval a c237 := h 236 (by decide)
  have h15 : Entails.eval a c449 := derived449 a h
  have h16 : Entails.eval a c194 := h 193 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  have h18 : Entails.eval a c621 := derived621 a h
  have h19 : Entails.eval a c139 := h 138 (by decide)
  have h20 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c508, some c622, some c125, some c295, some c284, some c291, some c624, some c195, some c193, some c237, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c561, c591, c357, c611, c463, c508, c622, c125, c295, c284, c291, c624, c195, c193, c237] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c622 := derived622 a h
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c291 := h 290 (by decide)
  have h11 : Entails.eval a c624 := derived624 a h
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c591, some c357, some c508, some c297, some c298, some c284, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c611, c591, c357, c508, c297, c298, c284] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c508 := derived508 a h
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c626, some c561, some c591, some c357, some c611, some c463, some c195, some c193, some c237, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c626, c561, c591, c357, c611, c463, c195, c193, c237] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c626 := derived626 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c463 := derived463 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨16, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c357, some c561, some c178, some c176, some c168, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c591, c357, c561, c178, c176, c168] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c561 := derived561 a h
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  have h5 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨25, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c628, some c132, some c185, some c186, some c168, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c561, c591, c357, c611, c463, c628, c132, c185, c186, c168] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c628 := derived628 a h
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c611, some c463, some c625, some c627, some c629, some c104, some c237, some c449, some c188, some c243, some c225, some c194, some c123, some c295, some c582, some c125, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c561, c591, c357, c611, c463, c625, c627, c629, c104, c237, c449, c188, c243, c225, c194, c123, c295, c582, c125] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c463 := derived463 a h
  have h5 : Entails.eval a c625 := derived625 a h
  have h6 : Entails.eval a c627 := derived627 a h
  have h7 : Entails.eval a c629 := derived629 a h
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c237 := h 236 (by decide)
  have h10 : Entails.eval a c449 := derived449 a h
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c582 := derived582 a h
  have h18 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c630, some c369, some c626, some c611, some c463, some c237, some c449, some c188, some c193, some c243, some c225, some c194, some c123, some c295, some c582, some c125, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c561, c591, c357, c630, c369, c626, c611, c463, c237, c449, c188, c193, c243, c225, c194, c123, c295, c582, c125] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c369 := derived369 a h
  have h5 : Entails.eval a c626 := derived626 a h
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c463 := derived463 a h
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c449 := derived449 a h
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c193 := h 192 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c225 := h 224 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  have h17 : Entails.eval a c582 := derived582 a h
  have h18 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c630, some c561, some c591, some c357, some c369, some c629, some c631, some c112, some c125, some c263, some c107, some c168, some c626, some c611, some c463, some c177, some c566, some c169, some c137, some c121, some c37, some c612, some c223, some c115, some c188, some c244, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c630, c561, c591, c357, c369, c629, c631, c112, c125, c263, c107, c168, c626, c611, c463, c177, c566, c169, c137, c121, c37, c612, c223, c115, c188, c244] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c630 := derived630 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c369 := derived369 a h
  have h5 : Entails.eval a c629 := derived629 a h
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c626 := derived626 a h
  have h13 : Entails.eval a c611 := derived611 a h
  have h14 : Entails.eval a c463 := derived463 a h
  have h15 : Entails.eval a c177 := h 176 (by decide)
  have h16 : Entails.eval a c566 := derived566 a h
  have h17 : Entails.eval a c169 := h 168 (by decide)
  have h18 : Entails.eval a c137 := h 136 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  have h20 : Entails.eval a c37 := h 36 (by decide)
  have h21 : Entails.eval a c612 := derived612 a h
  have h22 : Entails.eval a c223 := h 222 (by decide)
  have h23 : Entails.eval a c115 := h 114 (by decide)
  have h24 : Entails.eval a c188 := h 187 (by decide)
  have h25 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c630, some c369, some c629, some c631, some c112, some c611, some c463, some c125, some c295, some c263, some c107, some c632, some c132, some c97, some c612, some c239, some c115, some c194, some c244, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c561, c591, c357, c630, c369, c629, c631, c112, c611, c463, c125, c295, c263, c107, c632, c132, c97, c612, c239, c115, c194, c244] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c369 := derived369 a h
  have h5 : Entails.eval a c629 := derived629 a h
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c611 := derived611 a h
  have h9 : Entails.eval a c463 := derived463 a h
  have h10 : Entails.eval a c125 := h 124 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c632 := derived632 a h
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c97 := h 96 (by decide)
  have h17 : Entails.eval a c612 := derived612 a h
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c115 := h 114 (by decide)
  have h20 : Entails.eval a c194 := h 193 (by decide)
  have h21 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c633, some c561, some c591, some c357, some c630, some c369, some c629, some c631, some c112, some c508, some c43, some c129, some c284, some c12, some c265, some c39, some c208, some c263, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c633, c561, c591, c357, c630, c369, c629, c631, c112, c508, c43, c129, c284, c12, c265, c39, c208, c263] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c633 := derived633 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c630 := derived630 a h
  have h5 : Entails.eval a c369 := derived369 a h
  have h6 : Entails.eval a c629 := derived629 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c508 := derived508 a h
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c208 := h 207 (by decide)
  have h17 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨9, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c630, some c369, some c629, some c631, some c611, some c463, some c132, some c612, some c115, some c97, some c123, some c626, some c244, some c246, some c634, some c295, some c283, some c191, some c223, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c561, c591, c357, c630, c369, c629, c631, c611, c463, c132, c612, c115, c97, c123, c626, c244, c246, c634, c295, c283, c191, c223] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c369 := derived369 a h
  have h5 : Entails.eval a c629 := derived629 a h
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c611 := derived611 a h
  have h8 : Entails.eval a c463 := derived463 a h
  have h9 : Entails.eval a c132 := h 131 (by decide)
  have h10 : Entails.eval a c612 := derived612 a h
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c626 := derived626 a h
  have h15 : Entails.eval a c244 := h 243 (by decide)
  have h16 : Entails.eval a c246 := h 245 (by decide)
  have h17 : Entails.eval a c634 := derived634 a h
  have h18 : Entails.eval a c295 := h 294 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c191 := h 190 (by decide)
  have h21 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c561, some c591, some c357, some c630, some c369, some c626, some c611, some c463, some c123, some c97, some c635, some c193, some c243, some c223, some c194, some c283, some c295, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c561, c591, c357, c630, c369, c626, c611, c463, c123, c97, c635, c193, c243, c223, c194, c283, c295] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c561 := derived561 a h
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c369 := derived369 a h
  have h5 : Entails.eval a c626 := derived626 a h
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c463 := derived463 a h
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c635 := derived635 a h
  have h11 : Entails.eval a c193 := h 192 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c223 := h 222 (by decide)
  have h14 : Entails.eval a c194 := h 193 (by decide)
  have h15 : Entails.eval a c283 := h 282 (by decide)
  have h16 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c508, some c561, some c591, some c357, some c611, some c463, some c626, some c630, some c369, some c633, some c636, some c582, some c175, some c137, some c170, some c177, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c508, c561, c591, c357, c611, c463, c626, c630, c369, c633, c636, c582, c175, c137, c170, c177] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c508 := derived508 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c463 := derived463 a h
  have h6 : Entails.eval a c626 := derived626 a h
  have h7 : Entails.eval a c630 := derived630 a h
  have h8 : Entails.eval a c369 := derived369 a h
  have h9 : Entails.eval a c633 := derived633 a h
  have h10 : Entails.eval a c636 := derived636 a h
  have h11 : Entails.eval a c582 := derived582 a h
  have h12 : Entails.eval a c175 := h 174 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c170 := h 169 (by decide)
  have h15 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c177, some c179, some c118, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c177, c179, c118] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c177 := h 176 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c173, some c169, some c176, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c637, c173, c169, c176] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c173 := h 172 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  have h3 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c593, some c176, some c174, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c637, c593, c176, c174] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c593 := derived593 a h
  have h2 : Entails.eval a c176 := h 175 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c241, some c243, some c638, some c639, some c223, some c37, some c279, some c355, some c354, some c640, some c168, some c178, some c2, some c174, some c80, some c4, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c637, c241, c243, c638, c639, c223, c37, c279, c355, c354, c640, c168, c178, c2, c174, c80, c4] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c638 := derived638 a h
  have h4 : Entails.eval a c639 := derived639 a h
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c355 := h 354 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c640 := derived640 a h
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c2 := h 1 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c80 := h 79 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨22, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c117, some c249, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c121, c117, c249] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨54, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c348, some c279, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c354, c348, c279] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c348 := h 347 (by decide)
  have h2 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨52, by decide⟩, true), (⟨22, by decide⟩, true), (⟨9, by decide⟩, false), (⟨21, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c168, some c178, some c177, some c642, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c168, c178, c177, c642] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c168 := h 167 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c642 := derived642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨22, by decide⟩, true), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c643, some c644, some c640, some c350, some c355, some c279, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c643, c644, c640, c350, c355, c279] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c643 := derived643 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c640 := derived640 a h
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c44, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c637, c44] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c77, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c637, c77] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c83, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c637, c83] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c84, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c637, c84] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c130, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c637, c130] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c167, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c637, c167] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨14, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c173, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c637, c173] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨16, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c174, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c637, c174] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨50, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c281, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c637, c281] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨32, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c287, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c637, c287] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c637, some c288, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c637, c288] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c176, some c639, some c177, some c504, some c126, some c42, some c503, some c3, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c176, c639, c177, c504, c126, c42, c503, c3] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c176 := h 175 (by decide)
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c504 := derived504 a h
  have h4 : Entails.eval a c126 := h 125 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c503 := derived503 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived657

end CochromaticTwenty.Certificates.B16_7_1
