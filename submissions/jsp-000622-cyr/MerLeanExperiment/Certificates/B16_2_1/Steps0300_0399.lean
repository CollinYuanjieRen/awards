import MerLeanExperiment.Certificates.B16_2_1.Steps0200_0299

/-! Generated from the actual pinned b16_2_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c623 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c162, some c179, some c8, some c174, some c161, some c110, some c4, some c338, some c371, some c151, some c62, some c292, some c301, some c293, some c24, some c224, some c208, some c245, some c351, some c123, some c57, some c59, some c199, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c622, c162, c179, c8, c174, c161, c110, c4, c338, c371, c151, c62, c292, c301, c293, c24, c224, c208, c245, c351, c123, c57, c59, c199] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c161 := h 160 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c338 := derived338 a h
  have h9 : Entails.eval a c371 := derived371 a h
  have h10 : Entails.eval a c151 := h 150 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c301 := h 300 (by decide)
  have h14 : Entails.eval a c293 := h 292 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c208 := h 207 (by decide)
  have h18 : Entails.eval a c245 := h 244 (by decide)
  have h19 : Entails.eval a c351 := derived351 a h
  have h20 : Entails.eval a c123 := h 122 (by decide)
  have h21 : Entails.eval a c57 := h 56 (by decide)
  have h22 : Entails.eval a c59 := h 58 (by decide)
  have h23 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c162, some c28, some c19, some c174, some c179, some c161, some c623, some c64, some c74, some c223, some c301, some c303, some c27, some c524, some c75, some c320, some c94, some c82, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c622, c162, c28, c19, c174, c179, c161, c623, c64, c74, c223, c301, c303, c27, c524, c75, c320, c94, c82] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c179 := h 178 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c623 := derived623 a h
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c223 := h 222 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c303 := h 302 (by decide)
  have h13 : Entails.eval a c27 := h 26 (by decide)
  have h14 : Entails.eval a c524 := derived524 a h
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c320, some c78, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c315, c320, c78] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c19, some c162, some c624, some c10, some c169, some c141, some c170, some c16, some c164, some c62, some c8, some c94, some c625, some c520, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c622, c19, c162, c624, c10, c169, c141, c170, c16, c164, c62, c8, c94, c625, c520] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c624 := derived624 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c625 := derived625 a h
  have h14 : Entails.eval a c520 := derived520 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c506, some c496, some c6, some c65, some c86, some c94, some c10, some c177, some c301, some c303, some c25, some c180, some c113, some c161, some c63, some c524, some c292, some c75, some c225, some c428, some c300, some c371, some c208, some c244, some c351, some c123, some c126, some c57, some c41, some c119, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c622, c506, c496, c6, c65, c86, c94, c10, c177, c301, c303, c25, c180, c113, c161, c63, c524, c292, c75, c225, c428, c300, c371, c208, c244, c351, c123, c126, c57, c41, c119] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c506 := derived506 a h
  have h2 : Entails.eval a c496 := derived496 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c180 := h 179 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c524 := derived524 a h
  have h17 : Entails.eval a c292 := h 291 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c225 := h 224 (by decide)
  have h20 : Entails.eval a c428 := derived428 a h
  have h21 : Entails.eval a c300 := h 299 (by decide)
  have h22 : Entails.eval a c371 := derived371 a h
  have h23 : Entails.eval a c208 := h 207 (by decide)
  have h24 : Entails.eval a c244 := h 243 (by decide)
  have h25 : Entails.eval a c351 := derived351 a h
  have h26 : Entails.eval a c123 := h 122 (by decide)
  have h27 : Entails.eval a c126 := h 125 (by decide)
  have h28 : Entails.eval a c57 := h 56 (by decide)
  have h29 : Entails.eval a c41 := h 40 (by decide)
  have h30 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c315, some c320, some c1, some c172, some c171, some c161, some c15, some c176, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c622, c315, c320, c1, c172, c171, c161, c15, c176] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c142, some c301, some c10, some c74, some c154, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c142, c301, c10, c74, c154] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c142 := h 141 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c28, some c19, some c626, some c629, some c524, some c628, some c82, some c627, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c28, c19, c626, c629, c524, c628, c82, c627] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c626 := derived626 a h
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c524 := derived524 a h
  have h5 : Entails.eval a c628 := derived628 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c627 := derived627 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c506, some c625, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c506, c625] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c506 := derived506 a h
  have h1 : Entails.eval a c625 := derived625 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c631, some c96, some c63, some c568, some c301, some c302, some c315, some c297, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c622, c631, c96, c63, c568, c301, c302, c315, c297] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c568 := derived568 a h
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c315 := h 314 (by decide)
  have h8 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨55, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c97, some c83, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c96, c97, c83] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c632, some c524, some c302, some c67, some c633, some c526, some c142, some c10, some c9, some c176, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c622, c632, c524, c302, c67, c633, c526, c142, c10, c9, c176] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c632 := derived632 a h
  have h2 : Entails.eval a c524 := derived524 a h
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c633 := derived633 a h
  have h6 : Entails.eval a c526 := derived526 a h
  have h7 : Entails.eval a c142 := h 141 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c630, some c634, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c19, c630, c634] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c630 := derived630 a h
  have h2 : Entails.eval a c634 := derived634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c98, some c81, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c99, c98, c81] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c19, some c635, some c636, some c67, some c300, some c302, some c292, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c622, c19, c635, c636, c67, c300, c302, c292] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c635 := derived635 a h
  have h3 : Entails.eval a c636 := derived636 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c637, some c19, some c300, some c302, some c63, some c95, some c99, some c27, some c80, some c317, some c221, some c294, some c209, some c303, some c242, some c210, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c622, c637, c19, c300, c302, c63, c95, c99, c27, c80, c317, c221, c294, c209, c303, c242, c210] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c637 := derived637 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c294 := h 293 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c303 := h 302 (by decide)
  have h15 : Entails.eval a c242 := h 241 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c637, some c19, some c638, some c67, some c99, some c98, some c63, some c4, some c568, some c142, some c311, some c298, some c299, some c407, some c21, some c633, some c27, some c9, some c221, some c147, some c61, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c622, c637, c19, c638, c67, c99, c98, c63, c4, c568, c142, c311, c298, c299, c407, c21, c633, c27, c9, c221, c147, c61] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c637 := derived637 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c638 := derived638 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c568 := derived568 a h
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c407 := derived407 a h
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c633 := derived633 a h
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c9 := h 8 (by decide)
  have h19 : Entails.eval a c221 := h 220 (by decide)
  have h20 : Entails.eval a c147 := h 146 (by decide)
  have h21 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨44, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c568, some c495, some c629, some c311, some c633, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c4, c568, c495, c629, c311, c633] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c568 := derived568 a h
  have h2 : Entails.eval a c495 := derived495 a h
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨55, by decide⟩, true), (⟨43, by decide⟩, true), (⟨4, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c96, some c74, some c72, some c306, some c94, some c291, some c85, some c316, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c622, c96, c74, c72, c306, c94, c291, c85, c316] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c306 := h 305 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨43, by decide⟩, true), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c19, some c637, some c639, some c640, some c301, some c297, some c28, some c298, some c641, some c27, some c239, some c210, some c224, some c61, some c2, some c150, some c147, some c164, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c622, c19, c637, c639, c640, c301, c297, c28, c298, c641, c27, c239, c210, c224, c61, c2, c150, c147, c164] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c637 := derived637 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c640 := derived640 a h
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c641 := derived641 a h
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c239 := h 238 (by decide)
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c150 := h 149 (by decide)
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨4, by decide⟩, false), (⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c297, some c625, some c320, some c96, some c291, some c74, some c306, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c622, c297, c625, c320, c96, c291, c74, c306] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c297 := h 296 (by decide)
  have h2 : Entails.eval a c625 := derived625 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c639, some c637, some c19, some c301, some c640, some c643, some c298, some c642, some c299, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c622, c639, c637, c19, c301, c640, c643, c298, c642, c299] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c637 := derived637 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c640 := derived640 a h
  have h6 : Entails.eval a c643 := derived643 a h
  have h7 : Entails.eval a c298 := h 297 (by decide)
  have h8 : Entails.eval a c642 := derived642 a h
  have h9 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c190, some c187, some c41, some c57, some c183, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c190, c187, c41, c57, c183] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c190 := h 189 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨4, by decide⟩, false), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c303, some c299, some c67, some c96, some c24, some c74, some c72, some c94, some c7, some c85, some c144, some c316, some c226, some c10, some c291, some c209, some c148, some c242, some c245, some c113, some c161, some c179, some c645, some c46, some c48, some c127, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c622, c303, c299, c67, c96, c24, c74, c72, c94, c7, c85, c144, c316, c226, c10, c291, c209, c148, c242, c245, c113, c161, c179, c645, c46, c48, c127] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c144 := h 143 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c226 := h 225 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c242 := h 241 (by decide)
  have h19 : Entails.eval a c245 := h 244 (by decide)
  have h20 : Entails.eval a c113 := h 112 (by decide)
  have h21 : Entails.eval a c161 := h 160 (by decide)
  have h22 : Entails.eval a c179 := h 178 (by decide)
  have h23 : Entails.eval a c645 := derived645 a h
  have h24 : Entails.eval a c46 := h 45 (by decide)
  have h25 : Entails.eval a c48 := h 47 (by decide)
  have h26 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c644, some c63, some c639, some c28, some c637, some c19, some c294, some c299, some c646, some c27, some c239, some c241, some c209, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c644, c63, c639, c28, c637, c19, c294, c299, c646, c27, c239, c241, c209] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c637 := derived637 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c646 := derived646 a h
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c241 := h 240 (by decide)
  have h12 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c46, some c183, some c57, some c53, some c198, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c645, c46, c183, c57, c53, c198] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c183 := h 182 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨44, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c21, some c209, some c241, some c245, some c648, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c21, c209, c241, c245, c648] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c209 := h 208 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  have h3 : Entails.eval a c245 := h 244 (by decide)
  have h4 : Entails.eval a c648 := derived648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c639, some c28, some c637, some c19, some c67, some c644, some c63, some c647, some c311, some c317, some c1, some c79, some c78, some c291, some c226, some c96, some c649, some c299, some c141, some c304, some c74, some c75, some c143, some c94, some c13, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c622, c639, c28, c637, c19, c67, c644, c63, c647, c311, c317, c1, c79, c78, c291, c226, c96, c649, c299, c141, c304, c74, c75, c143, c94, c13] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c637 := derived637 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c644 := derived644 a h
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c647 := derived647 a h
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c226 := h 225 (by decide)
  have h16 : Entails.eval a c96 := h 95 (by decide)
  have h17 : Entails.eval a c649 := derived649 a h
  have h18 : Entails.eval a c299 := h 298 (by decide)
  have h19 : Entails.eval a c141 := h 140 (by decide)
  have h20 : Entails.eval a c304 := h 303 (by decide)
  have h21 : Entails.eval a c74 := h 73 (by decide)
  have h22 : Entails.eval a c75 := h 74 (by decide)
  have h23 : Entails.eval a c143 := h 142 (by decide)
  have h24 : Entails.eval a c94 := h 93 (by decide)
  have h25 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨21, by decide⟩, false), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c302, some c300, some c649, some c21, some c8, some c94, some c145, some c87, some c1, some c311, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c622, c302, c300, c649, c21, c8, c94, c145, c87, c1, c311] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c302 := h 301 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c649 := derived649 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨48, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨52, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c302, some c63, some c300, some c96, some c651, some c226, some c79, some c311, some c294, some c85, some c303, some c94, some c72, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c302, c63, c300, c96, c651, c226, c79, c311, c294, c85, c303, c94, c72] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c302 := h 301 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c651 := derived651 a h
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c637, some c639, some c28, some c650, some c300, some c302, some c652, some c27, some c239, some c241, some c209, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c19, c637, c639, c28, c650, c300, c302, c652, c27, c239, c241, c209] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c637 := derived637 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c652 := derived652 a h
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c239 := h 238 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c27, some c19, some c302, some c300, some c653, some c21, some c209, some c222, some c241, some c80, some c28, some c98, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c622, c27, c19, c302, c300, c653, c21, c209, c222, c241, c80, c28, c98] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c653 := derived653 a h
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c222 := h 221 (by decide)
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c19, some c302, some c300, some c27, some c654, some c239, some c221, some c28, some c80, some c99, some c98, some c71, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c622, c19, c302, c300, c27, c654, c239, c221, c28, c80, c99, c98, c71] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c654 := derived654 a h
  have h6 : Entails.eval a c239 := h 238 (by decide)
  have h7 : Entails.eval a c221 := h 220 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨2, by decide⟩, false), (⟨44, by decide⟩, true), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c95, some c71, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c93, c95, c71] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c311, some c313, some c85, some c84, some c97, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c79, c311, c313, c85, c84, c97] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨51, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c653, some c19, some c300, some c302, some c655, some c656, some c28, some c657, some c651, some c226, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c653, c19, c300, c302, c655, c656, c28, c657, c651, c226] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c653 := derived653 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c656 := derived656 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c657 := derived657 a h
  have h8 : Entails.eval a c651 := derived651 a h
  have h9 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨43, by decide⟩, true), (⟨21, by decide⟩, false), (⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c658, some c67, some c653, some c19, some c657, some c318, some c226, some c291, some c649, some c21, some c306, some c301, some c94, some c75, some c297, some c74, some c313, some c96, some c1, some c467, some c14, some c144, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c622, c658, c67, c653, c19, c657, c318, c226, c291, c649, c21, c306, c301, c94, c75, c297, c74, c313, c96, c1, c467, c14, c144] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c658 := derived658 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c653 := derived653 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c657 := derived657 a h
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c649 := derived649 a h
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c313 := h 312 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c1 := h 0 (by decide)
  have h20 : Entails.eval a c467 := derived467 a h
  have h21 : Entails.eval a c14 := h 13 (by decide)
  have h22 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨21, by decide⟩, false), (⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c658, some c653, some c19, some c659, some c93, some c95, some c656, some c21, some c407, some c301, some c244, some c97, some c297, some c214, some c313, some c230, some c467, some c32, some c12, some c14, some c111, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c622, c658, c653, c19, c659, c93, c95, c656, c21, c407, c301, c244, c97, c297, c214, c313, c230, c467, c32, c12, c14, c111] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c658 := derived658 a h
  have h2 : Entails.eval a c653 := derived653 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c656 := derived656 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c407 := derived407 a h
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c214 := h 213 (by decide)
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c467 := derived467 a h
  have h18 : Entails.eval a c32 := h 31 (by decide)
  have h19 : Entails.eval a c12 := h 11 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨9, by decide⟩, false), (⟨47, by decide⟩, true), (⟨2, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c95, some c405, some c12, some c97, some c142, some c73, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c93, c95, c405, c12, c97, c142, c73] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c405 := derived405 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨2, by decide⟩, false), (⟨48, by decide⟩, true), (⟨51, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c299, some c298, some c311, some c317, some c1, some c291, some c141, some c304, some c661, some c75, some c94, some c97, some c74, some c13, some c143, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c622, c299, c298, c311, c317, c1, c291, c141, c304, c661, c75, c94, c97, c74, c13, c143] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c661 := derived661 a h
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c74 := h 73 (by decide)
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c658, some c653, some c19, some c662, some c660, some c28, some c93, some c95, some c656, some c407, some c301, some c97, some c297, some c313, some c1, some c467, some c12, some c14, some c169, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c622, c658, c653, c19, c662, c660, c28, c93, c95, c656, c407, c301, c97, c297, c313, c1, c467, c12, c14, c169] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c658 := derived658 a h
  have h2 : Entails.eval a c653 := derived653 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c662 := derived662 a h
  have h5 : Entails.eval a c660 := derived660 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c407 := derived407 a h
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c313 := h 312 (by decide)
  have h15 : Entails.eval a c1 := h 0 (by decide)
  have h16 : Entails.eval a c467 := derived467 a h
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c14 := h 13 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c653, some c19, some c658, some c663, some c522, some c297, some c303, some c298, some c311, some c317, some c78, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c622, c653, c19, c658, c663, c522, c297, c303, c298, c311, c317, c78] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c653 := derived653 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c658 := derived658 a h
  have h4 : Entails.eval a c663 := derived663 a h
  have h5 : Entails.eval a c522 := derived522 a h
  have h6 : Entails.eval a c297 := h 296 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c311 := h 310 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, true), (⟨18, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c299, some c300, some c298, some c297, some c225, some c301, some c211, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c622, c299, c300, c298, c297, c225, c301, c211] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c297 := h 296 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c301 := h 300 (by decide)
  have h7 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨54, by decide⟩, true), (⟨18, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c222, some c665, some c293, some c301, some c303, some c209, some c211, some c240, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c222, c665, c293, c301, c303, c209, c211, c240] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c222 := h 221 (by decide)
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c293 := h 292 (by decide)
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c664, some c653, some c19, some c27, some c522, some c666, some c61, some c2, some c80, some c373, some c98, some c28, some c239, some c241, some c654, some c297, some c503, some c301, some c209, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c622, c664, c653, c19, c27, c522, c666, c61, c2, c80, c373, c98, c28, c239, c241, c654, c297, c503, c301, c209] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c664 := derived664 a h
  have h2 : Entails.eval a c653 := derived653 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c522 := derived522 a h
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c373 := derived373 a h
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  have h15 : Entails.eval a c654 := derived654 a h
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c503 := derived503 a h
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c48, some c127, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c46, c48, c127] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c190, some c187, some c41, some c57, some c119, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c190, c187, c41, c57, c119] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c190 := h 189 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c667, some c664, some c19, some c62, some c293, some c93, some c94, some c301, some c303, some c28, some c73, some c96, some c86, some c6, some c649, some c143, some c239, some c244, some c10, some c110, some c669, some c668, some c180, some c176, some c161, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c622, c667, c664, c19, c62, c293, c93, c94, c301, c303, c28, c73, c96, c86, c6, c649, c143, c239, c244, c10, c110, c669, c668, c180, c176, c161] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c664 := derived664 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c301 := h 300 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c86 := h 85 (by decide)
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c649 := derived649 a h
  have h16 : Entails.eval a c143 := h 142 (by decide)
  have h17 : Entails.eval a c239 := h 238 (by decide)
  have h18 : Entails.eval a c244 := h 243 (by decide)
  have h19 : Entails.eval a c10 := h 9 (by decide)
  have h20 : Entails.eval a c110 := h 109 (by decide)
  have h21 : Entails.eval a c669 := derived669 a h
  have h22 : Entails.eval a c668 := derived668 a h
  have h23 : Entails.eval a c180 := h 179 (by decide)
  have h24 : Entails.eval a c176 := h 175 (by decide)
  have h25 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c94, some c75, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c93, c94, c75] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c667, some c664, some c19, some c670, some c299, some c300, some c297, some c291, some c301, some c304, some c671, some c82, some c96, some c97, some c73, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c622, c667, c664, c19, c670, c299, c300, c297, c291, c301, c304, c671, c82, c96, c97, c73] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c664 := derived664 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c670 := derived670 a h
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c291 := h 290 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c671 := derived671 a h
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c97 := h 96 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c97, some c73, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c96, c97, c73] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨2, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c82, some c84, some c93, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c82, c84, c93] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c301, some c302, some c297, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c622, c301, c302, c297] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c664, some c653, some c19, some c672, some c318, some c674, some c675, some c673, some c299, some c303, some c293, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c667, c664, c653, c19, c672, c318, c674, c675, c673, c299, c303, c293] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c664 := derived664 a h
  have h2 : Entails.eval a c653 := derived653 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c672 := derived672 a h
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c674 := derived674 a h
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c673 := derived673 a h
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c22, some c142, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c14, c22, c142] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨4, by decide⟩, false), (⟨55, by decide⟩, false), (⟨5, by decide⟩, true), (⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c302, some c643, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c302, c643] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c302 := h 301 (by decide)
  have h1 : Entails.eval a c643 := derived643 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c653, some c676, some c313, some c1, some c319, some c667, some c664, some c19, some c299, some c303, some c144, some c62, some c93, some c94, some c443, some c28, some c7, some c16, some c229, some c677, some c96, some c74, some c628, some c395, some c678, some c209, some c244, some c110, some c239, some c669, some c668, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c653, c676, c313, c1, c319, c667, c664, c19, c299, c303, c144, c62, c93, c94, c443, c28, c7, c16, c229, c677, c96, c74, c628, c395, c678, c209, c244, c110, c239, c669, c668] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c653 := derived653 a h
  have h1 : Entails.eval a c676 := derived676 a h
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c664 := derived664 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c93 := h 92 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c443 := derived443 a h
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c229 := h 228 (by decide)
  have h19 : Entails.eval a c677 := derived677 a h
  have h20 : Entails.eval a c96 := h 95 (by decide)
  have h21 : Entails.eval a c74 := h 73 (by decide)
  have h22 : Entails.eval a c628 := derived628 a h
  have h23 : Entails.eval a c395 := derived395 a h
  have h24 : Entails.eval a c678 := derived678 a h
  have h25 : Entails.eval a c209 := h 208 (by decide)
  have h26 : Entails.eval a c244 := h 243 (by decide)
  have h27 : Entails.eval a c110 := h 109 (by decide)
  have h28 : Entails.eval a c239 := h 238 (by decide)
  have h29 : Entails.eval a c669 := derived669 a h
  have h30 : Entails.eval a c668 := derived668 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨8, by decide⟩, false), (⟨13, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c244, some c110, some c239, some c669, some c668, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c244, c110, c239, c669, c668] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c244 := h 243 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c239 := h 238 (by decide)
  have h3 : Entails.eval a c669 := derived669 a h
  have h4 : Entails.eval a c668 := derived668 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨44, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c667, some c679, some c673, some c653, some c676, some c313, some c1, some c319, some c19, some c93, some c94, some c443, some c671, some c28, some c73, some c25, some c66, some c229, some c233, some c628, some c24, some c143, some c15, some c395, some c680, some c209, some c300, some c304, some c291, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c622, c667, c679, c673, c653, c676, c313, c1, c319, c19, c93, c94, c443, c671, c28, c73, c25, c66, c229, c233, c628, c24, c143, c15, c395, c680, c209, c300, c304, c291] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c679 := derived679 a h
  have h3 : Entails.eval a c673 := derived673 a h
  have h4 : Entails.eval a c653 := derived653 a h
  have h5 : Entails.eval a c676 := derived676 a h
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c443 := derived443 a h
  have h13 : Entails.eval a c671 := derived671 a h
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c66 := h 65 (by decide)
  have h18 : Entails.eval a c229 := h 228 (by decide)
  have h19 : Entails.eval a c233 := h 232 (by decide)
  have h20 : Entails.eval a c628 := derived628 a h
  have h21 : Entails.eval a c24 := h 23 (by decide)
  have h22 : Entails.eval a c143 := h 142 (by decide)
  have h23 : Entails.eval a c15 := h 14 (by decide)
  have h24 : Entails.eval a c395 := derived395 a h
  have h25 : Entails.eval a c680 := derived680 a h
  have h26 : Entails.eval a c209 := h 208 (by decide)
  have h27 : Entails.eval a c300 := h 299 (by decide)
  have h28 : Entails.eval a c304 := h 303 (by decide)
  have h29 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, true), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c62, some c141, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c3, c62, c141] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c19, some c653, some c664, some c667, some c676, some c313, some c319, some c1, some c679, some c682, some c671, some c681, some c302, some c306, some c291, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c622, c19, c653, c664, c667, c676, c313, c319, c1, c679, c682, c671, c681, c302, c306, c291] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c653 := derived653 a h
  have h3 : Entails.eval a c664 := derived664 a h
  have h4 : Entails.eval a c667 := derived667 a h
  have h5 : Entails.eval a c676 := derived676 a h
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c679 := derived679 a h
  have h10 : Entails.eval a c682 := derived682 a h
  have h11 : Entails.eval a c671 := derived671 a h
  have h12 : Entails.eval a c681 := derived681 a h
  have h13 : Entails.eval a c302 := h 301 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨2, by decide⟩, false), (⟨41, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c675, some c302, some c671, some c298, some c306, some c320, some c291, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c622, c675, c302, c671, c298, c306, c320, c291] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c675 := derived675 a h
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c671 := derived671 a h
  have h4 : Entails.eval a c298 := h 297 (by decide)
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c60, some c302, some c67, some c98, some c301, some c467, some c94, some c684, some c144, some c7, some c14, some c678, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c622, c60, c302, c67, c98, c301, c467, c94, c684, c144, c7, c14, c678] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c467 := derived467 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c684 := derived684 a h
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c678 := derived678 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c60, some c302, some c675, some c67, some c442, some c685, some c522, some c78, some c625, some c525, some c316, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c622, c60, c302, c675, c67, c442, c685, c522, c78, c625, c525, c316] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c675 := derived675 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c442 := derived442 a h
  have h6 : Entails.eval a c685 := derived685 a h
  have h7 : Entails.eval a c522 := derived522 a h
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c625 := derived625 a h
  have h10 : Entails.eval a c525 := derived525 a h
  have h11 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨9, by decide⟩, false), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c302, some c675, some c142, some c313, some c315, some c298, some c164, some c144, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c622, c302, c675, c142, c313, c315, c298, c164, c144] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c302 := h 301 (by decide)
  have h2 : Entails.eval a c675 := derived675 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c298 := h 297 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c686, some c687, some c67, some c98, some c69, some c306, some c291, some c68, some c94, some c633, some c7, some c85, some c169, some c173, some c316, some c15, some c162, some c154, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c622, c686, c687, c67, c98, c69, c306, c291, c68, c94, c633, c7, c85, c169, c173, c316, c15, c162, c154] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c687 := derived687 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c633 := derived633 a h
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c686, some c687, some c683, some c313, some c218, some c688, some c310, some c69, some c93, some c98, some c68, some c8, some c80, some c530, some c307, some c170, some c162, some c216, some c316, some c210, some c583, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c622, c686, c687, c683, c313, c218, c688, c310, c69, c93, c98, c68, c8, c80, c530, c307, c170, c162, c216, c316, c210, c583] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c687 := derived687 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c688 := derived688 a h
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c530 := derived530 a h
  have h15 : Entails.eval a c307 := h 306 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c210 := h 209 (by decide)
  have h21 : Entails.eval a c583 := derived583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c686, some c687, some c69, some c93, some c98, some c68, some c8, some c80, some c530, some c307, some c170, some c295, some c316, some c318, some c162, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c622, c686, c687, c69, c93, c98, c68, c8, c80, c530, c307, c170, c295, c316, c318, c162] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c687 := derived687 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c530 := derived530 a h
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c295 := h 294 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c318 := h 317 (by decide)
  have h15 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c686, some c687, some c689, some c690, some c306, some c310, some c291, some c68, some c688, some c93, some c94, some c318, some c85, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c622, c686, c687, c689, c690, c306, c310, c291, c68, c688, c93, c94, c318, c85] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c687 := derived687 a h
  have h3 : Entails.eval a c689 := derived689 a h
  have h4 : Entails.eval a c690 := derived690 a h
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c688 := derived688 a h
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨50, by decide⟩, false), (⟨23, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c217, some c318, some c32, some c674, some c96, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c217, c318, c32, c674, c96] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c217 := h 216 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c674 := derived674 a h
  have h4 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c674, some c5, some c96, some c154, some c4, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c674, c5, c96, c154, c4] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c674 := derived674 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c683, some c686, some c687, some c691, some c311, some c315, some c219, some c690, some c306, some c310, some c291, some c68, some c67, some c93, some c94, some c34, some c692, some c693, some c223, some c208, some c245, some c397, some c244, some c104, some c351, some c123, some c57, some c59, some c199, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c622, c683, c686, c687, c691, c311, c315, c219, c690, c306, c310, c291, c68, c67, c93, c94, c34, c692, c693, c223, c208, c245, c397, c244, c104, c351, c123, c57, c59, c199] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c686 := derived686 a h
  have h3 : Entails.eval a c687 := derived687 a h
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c690 := derived690 a h
  have h9 : Entails.eval a c306 := h 305 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c93 := h 92 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c692 := derived692 a h
  have h18 : Entails.eval a c693 := derived693 a h
  have h19 : Entails.eval a c223 := h 222 (by decide)
  have h20 : Entails.eval a c208 := h 207 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c397 := derived397 a h
  have h23 : Entails.eval a c244 := h 243 (by decide)
  have h24 : Entails.eval a c104 := h 103 (by decide)
  have h25 : Entails.eval a c351 := derived351 a h
  have h26 : Entails.eval a c123 := h 122 (by decide)
  have h27 : Entails.eval a c57 := h 56 (by decide)
  have h28 : Entails.eval a c59 := h 58 (by decide)
  have h29 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c683, some c694, some c1, some c219, some c315, some c311, some c93, some c94, some c69, some c10, some c693, some c25, some c34, some c306, some c310, some c154, some c291, some c67, some c162, some c4, some c223, some c110, some c179, some c174, some c96, some c208, some c554, some c245, some c351, some c126, some c133, some c265, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c622, c683, c694, c1, c219, c315, c311, c93, c94, c69, c10, c693, c25, c34, c306, c310, c154, c291, c67, c162, c4, c223, c110, c179, c174, c96, c208, c554, c245, c351, c126, c133, c265] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c694 := derived694 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c219 := h 218 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c693 := derived693 a h
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c310 := h 309 (by decide)
  have h16 : Entails.eval a c154 := h 153 (by decide)
  have h17 : Entails.eval a c291 := h 290 (by decide)
  have h18 : Entails.eval a c67 := h 66 (by decide)
  have h19 : Entails.eval a c162 := h 161 (by decide)
  have h20 : Entails.eval a c4 := h 3 (by decide)
  have h21 : Entails.eval a c223 := h 222 (by decide)
  have h22 : Entails.eval a c110 := h 109 (by decide)
  have h23 : Entails.eval a c179 := h 178 (by decide)
  have h24 : Entails.eval a c174 := h 173 (by decide)
  have h25 : Entails.eval a c96 := h 95 (by decide)
  have h26 : Entails.eval a c208 := h 207 (by decide)
  have h27 : Entails.eval a c554 := derived554 a h
  have h28 : Entails.eval a c245 := h 244 (by decide)
  have h29 : Entails.eval a c351 := derived351 a h
  have h30 : Entails.eval a c126 := h 125 (by decide)
  have h31 : Entails.eval a c133 := h 132 (by decide)
  have h32 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨55, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c694, some c1, some c315, some c311, some c695, some c68, some c9, some c509, some c307, some c146, some c293, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c694, c1, c315, c311, c695, c68, c9, c509, c307, c146, c293] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c694 := derived694 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c695 := derived695 a h
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c509 := derived509 a h
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c696, some c694, some c1, some c315, some c68, some c306, some c307, some c69, some c295, some c98, some c318, some c80, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c622, c696, c694, c1, c315, c68, c306, c307, c69, c295, c98, c318, c80] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c696 := derived696 a h
  have h2 : Entails.eval a c694 := derived694 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c295 := h 294 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c694, some c1, some c683, some c311, some c315, some c219, some c696, some c697, some c93, some c94, some c69, some c692, some c306, some c310, some c291, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c622, c694, c1, c683, c311, c315, c219, c696, c697, c93, c94, c69, c692, c306, c310, c291] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c694 := derived694 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c219 := h 218 (by decide)
  have h7 : Entails.eval a c696 := derived696 a h
  have h8 : Entails.eval a c697 := derived697 a h
  have h9 : Entails.eval a c93 := h 92 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c692 := derived692 a h
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c698, some c93, some c94, some c69, some c85, some c306, some c310, some c318, some c291, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c622, c698, c93, c94, c69, c85, c306, c310, c318, c291] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c699, some c68, some c306, some c307, some c69, some c295, some c98, some c318, some c80, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c622, c699, c68, c306, c307, c69, c295, c98, c318, c80] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c699 := derived699 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c295 := h 294 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c700, some c698, some c694, some c68, some c9, some c306, some c307, some c147, some c69, some c295, some c164, some c98, some c175, some c80, some c509, some c316, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c622, c700, c698, c694, c68, c9, c306, c307, c147, c69, c295, c164, c98, c175, c80, c509, c316] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c694 := derived694 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c509 := derived509 a h
  have h16 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c698, some c700, some c701, some c94, some c633, some c7, some c66, some c554, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c698, c700, c701, c94, c633, c7, c66, c554] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c698 := derived698 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c633 := derived633 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c554 := derived554 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c694, some c1, some c683, some c702, some c218, some c313, some c698, some c93, some c94, some c633, some c69, some c10, some c83, some c7, some c85, some c66, some c87, some c24, some c33, some c306, some c310, some c154, some c680, some c158, some c291, some c316, some c223, some c162, some c208, some c174, some c179, some c245, some c351, some c126, some c132, some c264, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c622, c694, c1, c683, c702, c218, c313, c698, c93, c94, c633, c69, c10, c83, c7, c85, c66, c87, c24, c33, c306, c310, c154, c680, c158, c291, c316, c223, c162, c208, c174, c179, c245, c351, c126, c132, c264] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c694 := derived694 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c702 := derived702 a h
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c698 := derived698 a h
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c633 := derived633 a h
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c10 := h 9 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c87 := h 86 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c33 := h 32 (by decide)
  have h20 : Entails.eval a c306 := h 305 (by decide)
  have h21 : Entails.eval a c310 := h 309 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  have h23 : Entails.eval a c680 := derived680 a h
  have h24 : Entails.eval a c158 := h 157 (by decide)
  have h25 : Entails.eval a c291 := h 290 (by decide)
  have h26 : Entails.eval a c316 := h 315 (by decide)
  have h27 : Entails.eval a c223 := h 222 (by decide)
  have h28 : Entails.eval a c162 := h 161 (by decide)
  have h29 : Entails.eval a c208 := h 207 (by decide)
  have h30 : Entails.eval a c174 := h 173 (by decide)
  have h31 : Entails.eval a c179 := h 178 (by decide)
  have h32 : Entails.eval a c245 := h 244 (by decide)
  have h33 : Entails.eval a c351 := derived351 a h
  have h34 : Entails.eval a c126 := h 125 (by decide)
  have h35 : Entails.eval a c132 := h 131 (by decide)
  have h36 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c694, some c1, some c698, some c702, some c313, some c703, some c68, some c9, some c306, some c147, some c69, some c164, some c98, some c150, some c175, some c80, some c296, some c162, some c316, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c622, c694, c1, c698, c702, c313, c703, c68, c9, c306, c147, c69, c164, c98, c150, c175, c80, c296, c162, c316] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c694 := derived694 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c698 := derived698 a h
  have h4 : Entails.eval a c702 := derived702 a h
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c703 := derived703 a h
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c306 := h 305 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c175 := h 174 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c296 := h 295 (by decide)
  have h18 : Entails.eval a c162 := h 161 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c683, some c694, some c1, some c704, some c301, some c302, some c675, some c315, some c218, some c298, some c214, some c299, some c235, some c210, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c622, c683, c694, c1, c704, c301, c302, c675, c315, c218, c298, c214, c299, c235, c210] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c694 := derived694 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c704 := derived704 a h
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c218 := h 217 (by decide)
  have h10 : Entails.eval a c298 := h 297 (by decide)
  have h11 : Entails.eval a c214 := h 213 (by decide)
  have h12 : Entails.eval a c299 := h 298 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c675, some c302, some c301, some c705, some c683, some c298, some c299, some c62, some c21, some c72, some c216, some c1, some c467, some c144, some c7, some c164, some c97, some c522, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c622, c675, c302, c301, c705, c683, c298, c299, c62, c21, c72, c216, c1, c467, c144, c7, c164, c97, c522] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c675 := derived675 a h
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c301 := h 300 (by decide)
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c298 := h 297 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c467 := derived467 a h
  have h14 : Entails.eval a c144 := h 143 (by decide)
  have h15 : Entails.eval a c7 := h 6 (by decide)
  have h16 : Entails.eval a c164 := h 163 (by decide)
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c683, some c301, some c302, some c675, some c706, some c315, some c625, some c1, some c467, some c682, some c662, some c21, some c72, some c100, some c96, some c12, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c705, c683, c301, c302, c675, c706, c315, c625, c1, c467, c682, c662, c21, c72, c100, c96, c12] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c675 := derived675 a h
  have h5 : Entails.eval a c706 := derived706 a h
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c625 := derived625 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c467 := derived467 a h
  have h10 : Entails.eval a c682 := derived682 a h
  have h11 : Entails.eval a c662 := derived662 a h
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c100 := h 99 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨19, by decide⟩, true), (⟨9, by decide⟩, false), (⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c30, some c101, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c4, c30, c101] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨48, by decide⟩, false), (⟨5, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨3, by decide⟩, true), (⟨44, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c21, some c583, some c708, some c99, some c8, some c80, some c484, some c316, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c622, c21, c583, c708, c99, c8, c80, c484, c316] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c708 := derived708 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c484 := derived484 a h
  have h8 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c100, some c3, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c216, c100, c3] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c707, some c60, some c683, some c218, some c315, some c313, some c705, some c710, some c21, some c31, some c633, some c68, some c306, some c305, some c69, some c298, some c709, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c622, c707, c60, c683, c218, c315, c313, c705, c710, c21, c31, c633, c68, c306, c305, c69, c298, c709] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c707 := derived707 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c218 := h 217 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c705 := derived705 a h
  have h8 : Entails.eval a c710 := derived710 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c633 := derived633 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c305 := h 304 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  have h17 : Entails.eval a c709 := derived709 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c711, some c707, some c60, some c683, some c218, some c315, some c313, some c705, some c21, some c31, some c633, some c68, some c9, some c306, some c583, some c373, some c147, some c69, some c316, some c4, some c99, some c80, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c622, c711, c707, c60, c683, c218, c315, c313, c705, c21, c31, c633, c68, c9, c306, c583, c373, c147, c69, c316, c4, c99, c80] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c711 := derived711 a h
  have h2 : Entails.eval a c707 := derived707 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c683 := derived683 a h
  have h5 : Entails.eval a c218 := h 217 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c705 := derived705 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c633 := derived633 a h
  have h12 : Entails.eval a c68 := h 67 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c306 := h 305 (by decide)
  have h15 : Entails.eval a c583 := derived583 a h
  have h16 : Entails.eval a c373 := derived373 a h
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c69 := h 68 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c4 := h 3 (by decide)
  have h21 : Entails.eval a c99 := h 98 (by decide)
  have h22 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c707, some c60, some c712, some c216, some c711, some c705, some c68, some c9, some c373, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c683, c707, c60, c712, c216, c711, c705, c68, c9, c373] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c707 := derived707 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c712 := derived712 a h
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c711 := derived711 a h
  have h6 : Entails.eval a c705 := derived705 a h
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c373 := derived373 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c707, some c60, some c705, some c683, some c313, some c315, some c218, some c711, some c712, some c216, some c3, some c713, some c633, some c372, some c33, some c10, some c110, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c707, c60, c705, c683, c313, c315, c218, c711, c712, c216, c3, c713, c633, c372, c33, c10, c110] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c707 := derived707 a h
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c711 := derived711 a h
  have h8 : Entails.eval a c712 := derived712 a h
  have h9 : Entails.eval a c216 := h 215 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c713 := derived713 a h
  have h12 : Entails.eval a c633 := derived633 a h
  have h13 : Entails.eval a c372 := derived372 a h
  have h14 : Entails.eval a c33 := h 32 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c62, some c151, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c3, c62, c151] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c714, some c707, some c60, some c705, some c69, some c10, some c306, some c310, some c291, some c68, some c715, some c311, some c316, some c657, some c84, some c633, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c622, c714, c707, c60, c705, c69, c10, c306, c310, c291, c68, c715, c311, c316, c657, c84, c633] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c714 := derived714 a h
  have h2 : Entails.eval a c707 := derived707 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c715 := derived715 a h
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c316 := h 315 (by decide)
  have h14 : Entails.eval a c657 := derived657 a h
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨51, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c311, some c95, some c30, some c217, some c236, some c633, some c31, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c216, c311, c95, c30, c217, c236, c633, c31] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c217 := h 216 (by decide)
  have h5 : Entails.eval a c236 := h 235 (by decide)
  have h6 : Entails.eval a c633 := derived633 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c716, some c707, some c60, some c705, some c683, some c311, some c216, some c21, some c717, some c68, some c9, some c583, some c147, some c146, some c316, some c12, some c80, some c99, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c622, c716, c707, c60, c705, c683, c311, c216, c21, c717, c68, c9, c583, c147, c146, c316, c12, c80, c99] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c716 := derived716 a h
  have h2 : Entails.eval a c707 := derived707 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c717 := derived717 a h
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c583 := derived583 a h
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c146 := h 145 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c80 := h 79 (by decide)
  have h18 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c707, some c705, some c68, some c9, some c373, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c718, c707, c705, c68, c9, c373] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c707 := derived707 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c373 := derived373 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c714, some c707, some c60, some c705, some c683, some c716, some c718, some c82, some c719, some c372, some c95, some c97, some c217, some c32, some c30, some c234, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c714, c707, c60, c705, c683, c716, c718, c82, c719, c372, c95, c97, c217, c32, c30, c234] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c714 := derived714 a h
  have h1 : Entails.eval a c707 := derived707 a h
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c705 := derived705 a h
  have h4 : Entails.eval a c683 := derived683 a h
  have h5 : Entails.eval a c716 := derived716 a h
  have h6 : Entails.eval a c718 := derived718 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c719 := derived719 a h
  have h9 : Entails.eval a c372 := derived372 a h
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c217 := h 216 (by decide)
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c30 := h 29 (by decide)
  have h15 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨2, by decide⟩, false), (⟨9, by decide⟩, false), (⟨54, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c3, some c82, some c170, some c169, some c96, some c97, some c167, some c14, some c171, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c622, c3, c82, c170, c169, c96, c97, c167, c14, c171] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c170 := h 169 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c622, some c720, some c714, some c707, some c60, some c705, some c683, some c721, some c311, some c717, some c69, some c306, some c310, some c291, some c316, some c657, some c84, some c633, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c622, c720, c714, c707, c60, c705, c683, c721, c311, c717, c69, c306, c310, c291, c316, c657, c84, c633] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c622 := derived622 a h
  have h1 : Entails.eval a c720 := derived720 a h
  have h2 : Entails.eval a c714 := derived714 a h
  have h3 : Entails.eval a c707 := derived707 a h
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c705 := derived705 a h
  have h6 : Entails.eval a c683 := derived683 a h
  have h7 : Entails.eval a c721 := derived721 a h
  have h8 : Entails.eval a c311 := h 310 (by decide)
  have h9 : Entails.eval a c717 := derived717 a h
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c310 := h 309 (by decide)
  have h13 : Entails.eval a c291 := h 290 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c657 := derived657 a h
  have h16 : Entails.eval a c84 := h 83 (by decide)
  have h17 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived722

end CochromaticTwenty.Certificates.B16_2_1
