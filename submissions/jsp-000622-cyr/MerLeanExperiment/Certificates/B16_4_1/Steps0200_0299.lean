import MerLeanExperiment.Certificates.B16_4_1.Steps0100_0199

/-! Generated from the actual pinned b16_4_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c585 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c133, some c351, some c348, some c1, some c3, some c155, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c263, c133, c351, c348, c1, c3, c155] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c351 := h 350 (by decide)
  have h3 : Entails.eval a c348 := h 347 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c384, some c383, some c543, some c573, some c582, some c583, some c46, some c103, some c88, some c96, some c584, some c307, some c44, some c62, some c340, some c23, some c70, some c209, some c22, some c345, some c585, some c298, some c296, some c290, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c384, c383, c543, c573, c582, c583, c46, c103, c88, c96, c584, c307, c44, c62, c340, c23, c70, c209, c22, c345, c585, c298, c296, c290] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c384 := h 383 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c543 := derived543 a h
  have h3 : Entails.eval a c573 := derived573 a h
  have h4 : Entails.eval a c582 := derived582 a h
  have h5 : Entails.eval a c583 := derived583 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c584 := derived584 a h
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c340 := h 339 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c70 := h 69 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  have h18 : Entails.eval a c22 := h 21 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c585 := derived585 a h
  have h21 : Entails.eval a c298 := h 297 (by decide)
  have h22 : Entails.eval a c296 := h 295 (by decide)
  have h23 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨25, by decide⟩, true), (⟨49, by decide⟩, false), (⟨6, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c340, some c328, some c69, some c70, some c263, some c351, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c340, c328, c69, c70, c263, c351] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c573, some c582, some c583, some c383, some c586, some c50, some c89, some c510, some c298, some c96, some c587, some c72, some c71, some c327, some c351, some c263, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c543, c573, c582, c583, c383, c586, c50, c89, c510, c298, c96, c587, c72, c71, c327, c351, c263] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c573 := derived573 a h
  have h2 : Entails.eval a c582 := derived582 a h
  have h3 : Entails.eval a c583 := derived583 a h
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c586 := derived586 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c510 := derived510 a h
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c587 := derived587 a h
  have h12 : Entails.eval a c72 := h 71 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c588, some c49, some c307, some c543, some c582, some c583, some c46, some c91, some c103, some c286, some c374, some c377, some c88, some c96, some c44, some c328, some c585, some c263, some c68, some c70, some c349, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c573, c588, c49, c307, c543, c582, c583, c46, c91, c103, c286, c374, c377, c88, c96, c44, c328, c585, c263, c68, c70, c349] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c588 := derived588 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c543 := derived543 a h
  have h5 : Entails.eval a c582 := derived582 a h
  have h6 : Entails.eval a c583 := derived583 a h
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c103 := h 102 (by decide)
  have h10 : Entails.eval a c286 := h 285 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c44 := h 43 (by decide)
  have h16 : Entails.eval a c328 := h 327 (by decide)
  have h17 : Entails.eval a c585 := derived585 a h
  have h18 : Entails.eval a c263 := h 262 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c70 := h 69 (by decide)
  have h21 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c70, some c353, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c68, c70, c353] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c352, some c22, some c66, some c197, some c96, some c488, some c62, some c135, some c296, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c353, c352, c22, c66, c197, c96, c488, c62, c135, c296] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c488 := derived488 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨23, by decide⟩, false), (⟨33, by decide⟩, true), (⟨40, by decide⟩, false), (⟨30, by decide⟩, true), (⟨25, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c96, some c62, some c296, some c199, some c290, some c488, some c336, some c135, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c96, c62, c296, c199, c290, c488, c336, c135] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c96 := h 95 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c488 := derived488 a h
  have h6 : Entails.eval a c336 := h 335 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨25, by decide⟩, false), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c307, some c543, some c583, some c298, some c576, some c591, some c23, some c209, some c32, some c22, some c339, some c592, some c88, some c30, some c245, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c307, c543, c583, c298, c576, c591, c23, c209, c32, c22, c339, c592, c88, c30, c245] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c583 := derived583 a h
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c576 := derived576 a h
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c592 := derived592 a h
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c573, some c582, some c583, some c46, some c588, some c91, some c49, some c103, some c307, some c589, some c298, some c576, some c590, some c593, some c345, some c343, some c346, some c66, some c267, some c96, some c296, some c62, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c543, c573, c582, c583, c46, c588, c91, c49, c103, c307, c589, c298, c576, c590, c593, c345, c343, c346, c66, c267, c96, c296, c62] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c573 := derived573 a h
  have h2 : Entails.eval a c582 := derived582 a h
  have h3 : Entails.eval a c583 := derived583 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c588 := derived588 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c589 := derived589 a h
  have h11 : Entails.eval a c298 := h 297 (by decide)
  have h12 : Entails.eval a c576 := derived576 a h
  have h13 : Entails.eval a c590 := derived590 a h
  have h14 : Entails.eval a c593 := derived593 a h
  have h15 : Entails.eval a c345 := h 344 (by decide)
  have h16 : Entails.eval a c343 := h 342 (by decide)
  have h17 : Entails.eval a c346 := h 345 (by decide)
  have h18 : Entails.eval a c66 := h 65 (by decide)
  have h19 : Entails.eval a c267 := h 266 (by decide)
  have h20 : Entails.eval a c96 := h 95 (by decide)
  have h21 : Entails.eval a c296 := h 295 (by decide)
  have h22 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c543, some c582, some c583, some c46, some c594, some c95, some c104, some c91, some c89, some c383, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c573, c543, c582, c583, c46, c594, c95, c104, c91, c89, c383] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c582 := derived582 a h
  have h3 : Entails.eval a c583 := derived583 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c594 := derived594 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨7, by decide⟩, false), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c99, some c50, some c89, some c510, some c374, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c95, c99, c50, c89, c510, c374] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c510 := derived510 a h
  have h5 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c89, some c510, some c374, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c50, c89, c510, c374] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c510 := derived510 a h
  have h3 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨31, by decide⟩, true), (⟨53, by decide⟩, false), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c340, some c328, some c270, some c269, some c63, some c351, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c340, c328, c270, c269, c63, c351] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c340 := h 339 (by decide)
  have h1 : Entails.eval a c328 := h 327 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c573, some c596, some c595, some c597, some c104, some c46, some c85, some c303, some c304, some c374, some c377, some c292, some c88, some c290, some c106, some c302, some c598, some c44, some c26, some c65, some c299, some c208, some c37, some c21, some c327, some c347, some c270, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c543, c573, c596, c595, c597, c104, c46, c85, c303, c304, c374, c377, c292, c88, c290, c106, c302, c598, c44, c26, c65, c299, c208, c37, c21, c327, c347, c270] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c573 := derived573 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c597 := derived597 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c106 := h 105 (by decide)
  have h16 : Entails.eval a c302 := h 301 (by decide)
  have h17 : Entails.eval a c598 := derived598 a h
  have h18 : Entails.eval a c44 := h 43 (by decide)
  have h19 : Entails.eval a c26 := h 25 (by decide)
  have h20 : Entails.eval a c65 := h 64 (by decide)
  have h21 : Entails.eval a c299 := h 298 (by decide)
  have h22 : Entails.eval a c208 := h 207 (by decide)
  have h23 : Entails.eval a c37 := h 36 (by decide)
  have h24 : Entails.eval a c21 := h 20 (by decide)
  have h25 : Entails.eval a c327 := h 326 (by decide)
  have h26 : Entails.eval a c347 := h 346 (by decide)
  have h27 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c595, some c573, some c543, some c596, some c599, some c105, some c100, some c46, some c85, some c303, some c304, some c374, some c292, some c290, some c302, some c598, some c563, some c44, some c26, some c65, some c418, some c348, some c347, some c270, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c595, c573, c543, c596, c599, c105, c100, c46, c85, c303, c304, c374, c292, c290, c302, c598, c563, c44, c26, c65, c418, c348, c347, c270] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c595 := derived595 a h
  have h1 : Entails.eval a c573 := derived573 a h
  have h2 : Entails.eval a c543 := derived543 a h
  have h3 : Entails.eval a c596 := derived596 a h
  have h4 : Entails.eval a c599 := derived599 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  have h11 : Entails.eval a c374 := h 373 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c290 := h 289 (by decide)
  have h14 : Entails.eval a c302 := h 301 (by decide)
  have h15 : Entails.eval a c598 := derived598 a h
  have h16 : Entails.eval a c563 := derived563 a h
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c26 := h 25 (by decide)
  have h19 : Entails.eval a c65 := h 64 (by decide)
  have h20 : Entails.eval a c418 := derived418 a h
  have h21 : Entails.eval a c348 := h 347 (by decide)
  have h22 : Entails.eval a c347 := h 346 (by decide)
  have h23 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c374, some c290, some c600, some c573, some c46, some c303, some c302, some c292, some c43, some c598, some c327, some c37, some c63, some c299, some c351, some c271, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c543, c374, c290, c600, c573, c46, c303, c302, c292, c43, c598, c327, c37, c63, c299, c351, c271] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c573 := derived573 a h
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c598 := derived598 a h
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c299 := h 298 (by decide)
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c102, some c100, some c88, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c102, c100, c88] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c102 := h 101 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨30, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c50, some c600, some c595, some c573, some c374, some c377, some c290, some c602, some c46, some c601, some c303, some c302, some c97, some c292, some c43, some c88, some c327, some c96, some c62, some c299, some c264, some c133, some c340, some c3, some c65, some c138, some c351, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c543, c50, c600, c595, c573, c374, c377, c290, c602, c46, c601, c303, c302, c97, c292, c43, c88, c327, c96, c62, c299, c264, c133, c340, c3, c65, c138, c351] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c600 := derived600 a h
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c573 := derived573 a h
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c602 := derived602 a h
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c601 := derived601 a h
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c302 := h 301 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c62 := h 61 (by decide)
  have h20 : Entails.eval a c299 := h 298 (by decide)
  have h21 : Entails.eval a c264 := h 263 (by decide)
  have h22 : Entails.eval a c133 := h 132 (by decide)
  have h23 : Entails.eval a c340 := h 339 (by decide)
  have h24 : Entails.eval a c3 := h 2 (by decide)
  have h25 : Entails.eval a c65 := h 64 (by decide)
  have h26 : Entails.eval a c138 := h 137 (by decide)
  have h27 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨32, by decide⟩, false), (⟨39, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, true), (⟨30, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c65, some c211, some c351, some c22, some c269, some c349, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c26, c65, c211, c351, c22, c269, c349] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c97, some c46, some c303, some c292, some c383, some c384, some c290, some c88, some c538, some c96, some c43, some c62, some c299, some c604, some c340, some c269, some c264, some c346, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c50, c97, c46, c303, c292, c383, c384, c290, c88, c538, c96, c43, c62, c299, c604, c340, c269, c264, c346] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c538 := derived538 a h
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c62 := h 61 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c604 := derived604 a h
  have h15 : Entails.eval a c340 := h 339 (by decide)
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c264 := h 263 (by decide)
  have h18 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c384, some c88, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c383, c384, c88] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c80, some c354, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c75, c80, c354] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, false), (⟨46, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c358, some c465, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c360, c358, c465] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c465 := derived465 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨30, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c50, some c97, some c605, some c100, some c606, some c292, some c307, some c303, some c576, some c286, some c607, some c360, some c79, some c354, some c608, some c336, some c66, some c21, some c39, some c345, some c353, some c206, some c196, some c215, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c50, c97, c605, c100, c606, c292, c307, c303, c576, c286, c607, c360, c79, c354, c608, c336, c66, c21, c39, c345, c353, c206, c196, c215] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c605 := derived605 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c606 := derived606 a h
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c576 := derived576 a h
  have h9 : Entails.eval a c286 := h 285 (by decide)
  have h10 : Entails.eval a c607 := derived607 a h
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c608 := derived608 a h
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c206 := h 205 (by decide)
  have h22 : Entails.eval a c196 := h 195 (by decide)
  have h23 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨40, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c66, some c21, some c39, some c345, some c196, some c19, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c66, c21, c39, c345, c196, c19] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c66 := h 65 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨30, by decide⟩, true), (⟨56, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨28, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c609, some c45, some c85, some c299, some c102, some c100, some c606, some c292, some c303, some c576, some c610, some c336, some c343, some c88, some c19, some c339, some c197, some c22, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c609, c45, c85, c299, c102, c100, c606, c292, c303, c576, c610, c336, c343, c88, c19, c339, c197, c22] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c609 := derived609 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c299 := h 298 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c606 := derived606 a h
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c576 := derived576 a h
  have h10 : Entails.eval a c610 := derived610 a h
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c343 := h 342 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c339 := h 338 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c600, some c595, some c573, some c543, some c603, some c611, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c600, c595, c573, c543, c603, c611] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c600 := derived600 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c573 := derived573 a h
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c603 := derived603 a h
  have h5 : Entails.eval a c611 := derived611 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c573, some c595, some c612, some c510, some c304, some c374, some c377, some c46, some c602, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c573, c595, c612, c510, c304, c374, c377, c46, c602] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c573 := derived573 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c612 := derived612 a h
  have h3 : Entails.eval a c510 := derived510 a h
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c374 := h 373 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c602 := derived602 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c89, some c88, some c97, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c89, c88, c97] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c89 := h 88 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c25, some c243, some c237, some c72, some c29, some c328, some c264, some c488, some c352, some c418, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c613, c25, c243, c237, c72, c29, c328, c264, c488, c352, c418] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c488 := derived488 a h
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c418 := derived418 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c613, some c379, some c543, some c38, some c53, some c333, some c614, some c96, some c55, some c307, some c615, some c95, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c377, c613, c379, c543, c38, c53, c333, c614, c96, c55, c307, c615, c95] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c614 := derived614 a h
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c615 := derived615 a h
  have h12 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c377, some c614, some c96, some c95, some c49, some c41, some c566, some c331, some c72, some c263, some c327, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c543, c613, c379, c377, c614, c96, c95, c49, c41, c566, c331, c72, c263, c327] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c614 := derived614 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c566 := derived566 a h
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c613, some c379, some c616, some c602, some c543, some c614, some c95, some c96, some c617, some c307, some c44, some c328, some c133, some c263, some c172, some c173, some c333, some c143, some c70, some c590, some c7, some c353, some c156, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c377, c613, c379, c616, c602, c543, c614, c95, c96, c617, c307, c44, c328, c133, c263, c172, c173, c333, c143, c70, c590, c7, c353, c156] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c616 := derived616 a h
  have h4 : Entails.eval a c602 := derived602 a h
  have h5 : Entails.eval a c543 := derived543 a h
  have h6 : Entails.eval a c614 := derived614 a h
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c617 := derived617 a h
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c133 := h 132 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c172 := h 171 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c333 := h 332 (by decide)
  have h18 : Entails.eval a c143 := h 142 (by decide)
  have h19 : Entails.eval a c70 := h 69 (by decide)
  have h20 : Entails.eval a c590 := derived590 a h
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c353 := h 352 (by decide)
  have h23 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨50, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c331, some c349, some c91, some c22, some c103, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c331, c349, c91, c22, c103] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c331 := h 330 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨49, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c613, some c379, some c543, some c304, some c298, some c616, some c602, some c618, some c37, some c54, some c328, some c327, some c307, some c140, some c265, some c173, some c141, some c177, some c113, some c237, some c28, some c209, some c619, some c70, some c101, some c104, some c89, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c377, c613, c379, c543, c304, c298, c616, c602, c618, c37, c54, c328, c327, c307, c140, c265, c173, c141, c177, c113, c237, c28, c209, c619, c70, c101, c104, c89] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c616 := derived616 a h
  have h7 : Entails.eval a c602 := derived602 a h
  have h8 : Entails.eval a c618 := derived618 a h
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c307 := h 306 (by decide)
  have h14 : Entails.eval a c140 := h 139 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c141 := h 140 (by decide)
  have h18 : Entails.eval a c177 := h 176 (by decide)
  have h19 : Entails.eval a c113 := h 112 (by decide)
  have h20 : Entails.eval a c237 := h 236 (by decide)
  have h21 : Entails.eval a c28 := h 27 (by decide)
  have h22 : Entails.eval a c209 := h 208 (by decide)
  have h23 : Entails.eval a c619 := derived619 a h
  have h24 : Entails.eval a c70 := h 69 (by decide)
  have h25 : Entails.eval a c101 := h 100 (by decide)
  have h26 : Entails.eval a c104 := h 103 (by decide)
  have h27 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨7, by decide⟩, true), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c331, some c70, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c333, c331, c70] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c331 := h 330 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨28, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c377, some c379, some c602, some c543, some c48, some c103, some c91, some c89, some c101, some c621, some c289, some c134, some c177, some c7, some c146, some c296, some c587, some c265, some c306, some c54, some c617, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c613, c377, c379, c602, c543, c48, c103, c91, c89, c101, c621, c289, c134, c177, c7, c146, c296, c587, c265, c306, c54, c617] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c602 := derived602 a h
  have h4 : Entails.eval a c543 := derived543 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c621 := derived621 a h
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c177 := h 176 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c587 := derived587 a h
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c306 := h 305 (by decide)
  have h20 : Entails.eval a c54 := h 53 (by decide)
  have h21 : Entails.eval a c617 := derived617 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨49, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c620, some c48, some c613, some c379, some c289, some c543, some c602, some c103, some c89, some c101, some c622, some c305, some c301, some c60, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c377, c620, c48, c613, c379, c289, c543, c602, c103, c89, c101, c622, c305, c301, c60] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c613 := derived613 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c602 := derived602 a h
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c101 := h 100 (by decide)
  have h11 : Entails.eval a c622 := derived622 a h
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c301 := h 300 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨31, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c49, some c41, some c566, some c331, some c65, some c98, some c54, some c63, some c297, some c327, some c272, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c613, c49, c41, c566, c331, c65, c98, c54, c63, c297, c327, c272] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c566 := derived566 a h
  have h4 : Entails.eval a c331 := h 330 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c297 := h 296 (by decide)
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨29, by decide⟩, true), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c333, some c268, some c270, some c349, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c333, c268, c270, c349] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c333 := h 332 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨49, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c623, some c377, some c620, some c48, some c613, some c379, some c289, some c543, some c305, some c301, some c624, some c106, some c625, some c65, some c328, some c561, some c63, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c623, c377, c620, c48, c613, c379, c289, c543, c305, c301, c624, c106, c625, c65, c328, c561, c63] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c623 := derived623 a h
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c613 := derived613 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c543 := derived543 a h
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c624 := derived624 a h
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c625 := derived625 a h
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c328 := h 327 (by decide)
  have h15 : Entails.eval a c561 := derived561 a h
  have h16 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨28, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c38, some c333, some c377, some c48, some c379, some c289, some c543, some c625, some c296, some c53, some c614, some c98, some c95, some c55, some c615, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c613, c38, c333, c377, c48, c379, c289, c543, c625, c296, c53, c614, c98, c95, c55, c615] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c543 := derived543 a h
  have h8 : Entails.eval a c625 := derived625 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c614 := derived614 a h
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  have h14 : Entails.eval a c55 := h 54 (by decide)
  have h15 : Entails.eval a c615 := derived615 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c379, some c377, some c620, some c289, some c48, some c623, some c626, some c38, some c333, some c627, some c306, some c55, some c106, some c98, some c53, some c300, some c268, some c272, some c349, some c328, some c64, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c613, c379, c377, c620, c289, c48, c623, c626, c38, c333, c627, c306, c55, c106, c98, c53, c300, c268, c272, c349, c328, c64] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  have h3 : Entails.eval a c620 := derived620 a h
  have h4 : Entails.eval a c289 := h 288 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c623 := derived623 a h
  have h7 : Entails.eval a c626 := derived626 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c627 := derived627 a h
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c53 := h 52 (by decide)
  have h16 : Entails.eval a c300 := h 299 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c272 := h 271 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨39, by decide⟩, true), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c272, some c330, some c349, some c345, some c48, some c106, some c98, some c64, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c268, c272, c330, c349, c345, c48, c106, c98, c64] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c330 := h 329 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c40, some c330, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c48, c40, c330] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c38, some c630, some c333, some c379, some c543, some c98, some c97, some c55, some c89, some c306, some c95, some c289, some c72, some c380, some c554, some c91, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c613, c38, c630, c333, c379, c543, c98, c97, c55, c89, c306, c95, c289, c72, c380, c554, c91] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c630 := derived630 a h
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c543 := derived543 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c380 := h 379 (by decide)
  have h15 : Entails.eval a c554 := derived554 a h
  have h16 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c38, some c333, some c628, some c379, some c631, some c45, some c300, some c268, some c330, some c289, some c306, some c55, some c629, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c613, c38, c333, c628, c379, c631, c45, c300, c268, c330, c289, c306, c55, c629] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c628 := derived628 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c300 := h 299 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c330 := h 329 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c55 := h 54 (by decide)
  have h13 : Entails.eval a c629 := derived629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c38, some c333, some c628, some c379, some c543, some c630, some c632, some c625, some c300, some c45, some c287, some c98, some c97, some c331, some c89, some c41, some c137, some c264, some c95, some c14, some c72, some c136, some c345, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c613, c38, c333, c628, c379, c543, c630, c632, c625, c300, c45, c287, c98, c97, c331, c89, c41, c137, c264, c95, c14, c72, c136, c345] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c628 := derived628 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c543 := derived543 a h
  have h6 : Entails.eval a c630 := derived630 a h
  have h7 : Entails.eval a c632 := derived632 a h
  have h8 : Entails.eval a c625 := derived625 a h
  have h9 : Entails.eval a c300 := h 299 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c287 := h 286 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c331 := h 330 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c264 := h 263 (by decide)
  have h19 : Entails.eval a c95 := h 94 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c72 := h 71 (by decide)
  have h22 : Entails.eval a c136 := h 135 (by decide)
  have h23 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨28, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c613, some c38, some c333, some c379, some c543, some c55, some c307, some c287, some c384, some c331, some c614, some c41, some c137, some c264, some c95, some c11, some c72, some c25, some c343, some c243, some c418, some c29, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c45, c613, c38, c333, c379, c543, c55, c307, c287, c384, c331, c614, c41, c137, c264, c95, c11, c72, c25, c343, c243, c418, c29] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c543 := derived543 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c331 := h 330 (by decide)
  have h11 : Entails.eval a c614 := derived614 a h
  have h12 : Entails.eval a c41 := h 40 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c264 := h 263 (by decide)
  have h15 : Entails.eval a c95 := h 94 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c25 := h 24 (by decide)
  have h19 : Entails.eval a c343 := h 342 (by decide)
  have h20 : Entails.eval a c243 := h 242 (by decide)
  have h21 : Entails.eval a c418 := derived418 a h
  have h22 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c628, some c613, some c379, some c543, some c38, some c333, some c633, some c298, some c45, some c634, some c98, some c96, some c89, some c88, some c99, some c330, some c68, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c628, c613, c379, c543, c38, c333, c633, c298, c45, c634, c98, c96, c89, c88, c99, c330, c68] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c628 := derived628 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c333 := h 332 (by decide)
  have h6 : Entails.eval a c633 := derived633 a h
  have h7 : Entails.eval a c298 := h 297 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c634 := derived634 a h
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c330 := h 329 (by decide)
  have h16 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨1, by decide⟩, false), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c96, some c58, some c89, some c99, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c98, c96, c58, c89, c99] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c95, some c89, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c99, c95, c89] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨24, by decide⟩, false), (⟨40, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c2, some c418, some c144, some c352, some c301, some c561, some c41, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c1, c2, c418, c144, c352, c301, c561, c41] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c418 := derived418 a h
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c301 := h 300 (by decide)
  have h6 : Entails.eval a c561 := derived561 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c635, some c305, some c304, some c613, some c379, some c543, some c636, some c637, some c58, some c43, some c62, some c97, some c333, some c89, some c65, some c20, some c204, some c24, some c35, some c346, some c638, some c133, some c107, some c200, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c635, c305, c304, c613, c379, c543, c636, c637, c58, c43, c62, c97, c333, c89, c65, c20, c204, c24, c35, c346, c638, c133, c107, c200] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c635 := derived635 a h
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c613 := derived613 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c543 := derived543 a h
  have h6 : Entails.eval a c636 := derived636 a h
  have h7 : Entails.eval a c637 := derived637 a h
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c24 := h 23 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  have h20 : Entails.eval a c638 := derived638 a h
  have h21 : Entails.eval a c133 := h 132 (by decide)
  have h22 : Entails.eval a c107 := h 106 (by decide)
  have h23 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c305, some c304, some c20, some c63, some c65, some c204, some c345, some c136, some c268, some c15, some c346, some c112, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c305, c304, c20, c63, c65, c204, c345, c136, c268, c15, c346, c112] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c305 := h 304 (by decide)
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c136 := h 135 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c333, some c625, some c268, some c301, some c330, some c289, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c379, c333, c625, c268, c301, c330, c289] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c333 := h 332 (by decide)
  have h2 : Entails.eval a c625 := derived625 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨34, by decide⟩, true), (⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c63, some c304, some c65, some c640, some c345, some c40, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c63, c304, c65, c640, c345, c40] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c640 := derived640 a h
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c380, some c240, some c86, some c105, some c56, some c30, some c201, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c48, c380, c240, c86, c105, c56, c30, c201] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, true), (⟨33, by decide⟩, false), (⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c613, some c379, some c643, some c550, some c106, some c384, some c241, some c23, some c28, some c289, some c340, some c196, some c297, some c272, some c346, some c342, some c218, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c45, c613, c379, c643, c550, c106, c384, c241, c23, c28, c289, c340, c196, c297, c272, c346, c342, c218] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c643 := derived643 a h
  have h4 : Entails.eval a c550 := derived550 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c289 := h 288 (by decide)
  have h11 : Entails.eval a c340 := h 339 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c346 := h 345 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c628, some c613, some c635, some c304, some c305, some c639, some c641, some c20, some c63, some c204, some c644, some c65, some c642, some c345, some c24, some c268, some c346, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c628, c613, c635, c304, c305, c639, c641, c20, c63, c204, c644, c65, c642, c345, c24, c268, c346] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c628 := derived628 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c635 := derived635 a h
  have h3 : Entails.eval a c304 := h 303 (by decide)
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c639 := derived639 a h
  have h6 : Entails.eval a c641 := derived641 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c644 := derived644 a h
  have h11 : Entails.eval a c65 := h 64 (by decide)
  have h12 : Entails.eval a c642 := derived642 a h
  have h13 : Entails.eval a c345 := h 344 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c379, some c543, some c89, some c100, some c101, some c60, some c91, some c58, some c384, some c621, some c567, some c289, some c297, some c301, some c265, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c613, c379, c543, c89, c100, c101, c60, c91, c58, c384, c621, c567, c289, c297, c301, c265] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c543 := derived543 a h
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c621 := derived621 a h
  have h11 : Entails.eval a c567 := derived567 a h
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c297 := h 296 (by decide)
  have h14 : Entails.eval a c301 := h 300 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨56, by decide⟩, false), (⟨25, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c646, some c104, some c103, some c58, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c646, c104, c103, c58] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c646 := derived646 a h
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c628, some c45, some c298, some c300, some c647, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c645, c628, c45, c298, c300, c647] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c628 := derived628 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c647 := derived647 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c648, some c637, some c645, some c636, some c58, some c62, some c97, some c102, some c60, some c91, some c306, some c384, some c289, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c543, c613, c379, c648, c637, c645, c636, c58, c62, c97, c102, c60, c91, c306, c384, c289] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c648 := derived648 a h
  have h4 : Entails.eval a c637 := derived637 a h
  have h5 : Entails.eval a c645 := derived645 a h
  have h6 : Entails.eval a c636 := derived636 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c384 := h 383 (by decide)
  have h15 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c300, some c305, some c543, some c613, some c379, some c648, some c637, some c645, some c89, some c100, some c96, some c91, some c384, some c621, some c558, some c263, some c72, some c71, some c346, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c649, c300, c305, c543, c613, c379, c648, c637, c645, c89, c100, c96, c91, c384, c621, c558, c263, c72, c71, c346] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c300 := h 299 (by decide)
  have h2 : Entails.eval a c305 := h 304 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c613 := derived613 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c648 := derived648 a h
  have h7 : Entails.eval a c637 := derived637 a h
  have h8 : Entails.eval a c645 := derived645 a h
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c91 := h 90 (by decide)
  have h13 : Entails.eval a c384 := h 383 (by decide)
  have h14 : Entails.eval a c621 := derived621 a h
  have h15 : Entails.eval a c558 := derived558 a h
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c72 := h 71 (by decide)
  have h18 : Entails.eval a c71 := h 70 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c648, some c645, some c628, some c613, some c649, some c305, some c300, some c650, some c97, some c48, some c40, some c630, some c380, some c339, some c134, some c287, some c265, some c175, some c306, some c56, some c144, some c6, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c648, c645, c628, c613, c649, c305, c300, c650, c97, c48, c40, c630, c380, c339, c134, c287, c265, c175, c306, c56, c144, c6] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c648 := derived648 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c628 := derived628 a h
  have h3 : Entails.eval a c613 := derived613 a h
  have h4 : Entails.eval a c649 := derived649 a h
  have h5 : Entails.eval a c305 := h 304 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c630 := derived630 a h
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c339 := h 338 (by decide)
  have h14 : Entails.eval a c134 := h 133 (by decide)
  have h15 : Entails.eval a c287 := h 286 (by decide)
  have h16 : Entails.eval a c265 := h 264 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c306 := h 305 (by decide)
  have h19 : Entails.eval a c56 := h 55 (by decide)
  have h20 : Entails.eval a c144 := h 143 (by decide)
  have h21 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨32, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c134, some c263, some c265, some c175, some c345, some c343, some c154, some c66, some c6, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c134, c263, c265, c175, c345, c343, c154, c66, c6] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c134 := h 133 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c175 := h 174 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c343 := h 342 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  have h8 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c287, some c307, some c652, some c333, some c330, some c68, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c380, c287, c307, c652, c333, c330, c68] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c652 := derived652 a h
  have h4 : Entails.eval a c333 := h 332 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c590, some c72, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c590, c72] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c637, some c97, some c653, some c614, some c602, some c96, some c654, some c333, some c585, some c346, some c342, some c134, some c9, some c6, some c155, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c379, c637, c97, c653, c614, c602, c96, c654, c333, c585, c346, c342, c134, c9, c6, c155] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c637 := derived637 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c653 := derived653 a h
  have h4 : Entails.eval a c614 := derived614 a h
  have h5 : Entails.eval a c602 := derived602 a h
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c654 := derived654 a h
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c585 := derived585 a h
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c342 := h 341 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c71, some c340, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c69, c71, c340] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c379, some c543, some c628, some c645, some c648, some c637, some c651, some c304, some c298, some c655, some c89, some c100, some c96, some c91, some c621, some c263, some c656, some c346, some c70, some c72, some c340, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c613, c379, c543, c628, c645, c648, c637, c651, c304, c298, c655, c89, c100, c96, c91, c621, c263, c656, c346, c70, c72, c340] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c379 := h 378 (by decide)
  have h2 : Entails.eval a c543 := derived543 a h
  have h3 : Entails.eval a c628 := derived628 a h
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c648 := derived648 a h
  have h6 : Entails.eval a c637 := derived637 a h
  have h7 : Entails.eval a c651 := derived651 a h
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c655 := derived655 a h
  have h11 : Entails.eval a c89 := h 88 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c96 := h 95 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c621 := derived621 a h
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c656 := derived656 a h
  have h18 : Entails.eval a c346 := h 345 (by decide)
  have h19 : Entails.eval a c70 := h 69 (by decide)
  have h20 : Entails.eval a c72 := h 71 (by decide)
  have h21 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c96, some c654, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c100, c96, c654] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c654 := derived654 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c657, some c50, some c97, some c613, some c379, some c637, some c290, some c43, some c68, some c302, some c296, some c658, some c88, some c606, some c377, some c330, some c547, some c652, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c543, c657, c50, c97, c613, c379, c637, c290, c43, c68, c302, c296, c658, c88, c606, c377, c330, c547, c652] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c657 := derived657 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c613 := derived613 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c637 := derived637 a h
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c658 := derived658 a h
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c606 := derived606 a h
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c330 := h 329 (by decide)
  have h17 : Entails.eval a c547 := derived547 a h
  have h18 : Entails.eval a c652 := derived652 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c659, some c333, some c543, some c657, some c50, some c97, some c379, some c637, some c290, some c88, some c606, some c377, some c292, some c547, some c301, some c576, some c652, some c339, some c40, some c22, some c66, some c240, some c197, some c343, some c214, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c613, c659, c333, c543, c657, c50, c97, c379, c637, c290, c88, c606, c377, c292, c547, c301, c576, c652, c339, c40, c22, c66, c240, c197, c343, c214] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c379 := h 378 (by decide)
  have h8 : Entails.eval a c637 := derived637 a h
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c606 := derived606 a h
  have h12 : Entails.eval a c377 := h 376 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c547 := derived547 a h
  have h15 : Entails.eval a c301 := h 300 (by decide)
  have h16 : Entails.eval a c576 := derived576 a h
  have h17 : Entails.eval a c652 := derived652 a h
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c40 := h 39 (by decide)
  have h20 : Entails.eval a c22 := h 21 (by decide)
  have h21 : Entails.eval a c66 := h 65 (by decide)
  have h22 : Entails.eval a c240 := h 239 (by decide)
  have h23 : Entails.eval a c197 := h 196 (by decide)
  have h24 : Entails.eval a c343 := h 342 (by decide)
  have h25 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c296, some c297, some c62, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c296, c297, c62] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c296 := h 295 (by decide)
  have h1 : Entails.eval a c297 := h 296 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c290, some c637, some c660, some c96, some c661, some c659, some c333, some c50, some c97, some c44, some c62, some c302, some c585, some c652, some c328, some c48, some c655, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c543, c613, c379, c657, c290, c637, c660, c96, c661, c659, c333, c50, c97, c44, c62, c302, c585, c652, c328, c48, c655] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c637 := derived637 a h
  have h6 : Entails.eval a c660 := derived660 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c661 := derived661 a h
  have h9 : Entails.eval a c659 := derived659 a h
  have h10 : Entails.eval a c333 := h 332 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c97 := h 96 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c585 := derived585 a h
  have h17 : Entails.eval a c652 := derived652 a h
  have h18 : Entails.eval a c328 := h 327 (by decide)
  have h19 : Entails.eval a c48 := h 47 (by decide)
  have h20 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c657, some c50, some c97, some c613, some c379, some c637, some c290, some c660, some c100, some c96, some c661, some c662, some c306, some c292, some c60, some c384, some c302, some c48, some c617, some c655, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c543, c657, c50, c97, c613, c379, c637, c290, c660, c100, c96, c661, c662, c306, c292, c60, c384, c302, c48, c617, c655] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c657 := derived657 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c613 := derived613 a h
  have h5 : Entails.eval a c379 := h 378 (by decide)
  have h6 : Entails.eval a c637 := derived637 a h
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c660 := derived660 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c661 := derived661 a h
  have h12 : Entails.eval a c662 := derived662 a h
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c384 := h 383 (by decide)
  have h17 : Entails.eval a c302 := h 301 (by decide)
  have h18 : Entails.eval a c48 := h 47 (by decide)
  have h19 : Entails.eval a c617 := derived617 a h
  have h20 : Entails.eval a c655 := derived655 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c616, some c634, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c616, c634] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c616 := derived616 a h
  have h1 : Entails.eval a c634 := derived634 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c290, some c637, some c661, some c663, some c50, some c97, some c664, some c302, some c43, some c333, some c20, some c202, some c243, some c32, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c543, c613, c379, c657, c290, c637, c661, c663, c50, c97, c664, c302, c43, c333, c20, c202, c243, c32] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c637 := derived637 a h
  have h6 : Entails.eval a c661 := derived661 a h
  have h7 : Entails.eval a c663 := derived663 a h
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c664 := derived664 a h
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c333 := h 332 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c243 := h 242 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c663, some c543, some c657, some c50, some c97, some c613, some c665, some c48, some c40, some c630, some c339, some c65, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c663, c543, c657, c50, c97, c613, c665, c48, c40, c630, c339, c65] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c663 := derived663 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c657 := derived657 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c613 := derived613 a h
  have h6 : Entails.eval a c665 := derived665 a h
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c630 := derived630 a h
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c290, some c50, some c637, some c97, some c663, some c666, some c96, some c88, some c606, some c292, some c301, some c38, some c333, some c330, some c68, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c543, c613, c379, c657, c290, c50, c637, c97, c663, c666, c96, c88, c606, c292, c301, c38, c333, c330, c68] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c637 := derived637 a h
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c663 := derived663 a h
  have h9 : Entails.eval a c666 := derived666 a h
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c606 := derived606 a h
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c301 := h 300 (by decide)
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c330 := h 329 (by decide)
  have h18 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c88, some c606, some c377, some c292, some c45, some c301, some c38, some c630, some c330, some c22, some c240, some c197, some c27, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c667, c543, c613, c379, c657, c290, c88, c606, c377, c292, c45, c301, c38, c630, c330, c22, c240, c197, c27] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c606 := derived606 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c630 := derived630 a h
  have h14 : Entails.eval a c330 := h 329 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c240 := h 239 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c86, some c292, some c301, some c306, some c38, some c53, some c333, some c296, some c139, some c272, some c172, some c328, some c470, some c64, some c21, some c352, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c667, c543, c613, c379, c657, c290, c86, c292, c301, c306, c38, c53, c333, c296, c139, c272, c172, c328, c470, c64, c21, c352] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c301 := h 300 (by decide)
  have h9 : Entails.eval a c306 := h 305 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c296 := h 295 (by decide)
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c272 := h 271 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c470 := derived470 a h
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c333, some c331, some c41, some c64, some c301, some c306, some c328, some c53, some c272, some c296, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c667, c543, c613, c379, c657, c290, c333, c331, c41, c64, c301, c306, c328, c53, c272, c296] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c333 := h 332 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c272 := h 271 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c290, some c670, some c38, some c302, some c301, some c624, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c543, c613, c379, c657, c290, c670, c38, c302, c301, c624] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c670 := derived670 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  have h8 : Entails.eval a c301 := h 300 (by decide)
  have h9 : Entails.eval a c624 := derived624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c290, some c667, some c668, some c669, some c671, some c45, some c297, some c296, some c20, some c38, some c63, some c201, some c301, some c21, some c566, some c342, some c272, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c543, c613, c379, c657, c290, c667, c668, c669, c671, c45, c297, c296, c20, c38, c63, c201, c301, c21, c566, c342, c272] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c668 := derived668 a h
  have h7 : Entails.eval a c669 := derived669 a h
  have h8 : Entails.eval a c671 := derived671 a h
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c20 := h 19 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c63 := h 62 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  have h18 : Entails.eval a c566 := derived566 a h
  have h19 : Entails.eval a c342 := h 341 (by decide)
  have h20 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c668, some c106, some c669, some c671, some c45, some c296, some c297, some c672, some c333, some c331, some c629, some c272, some c41, some c23, some c64, some c209, some c345, some c343, some c206, some c217, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c667, c543, c613, c379, c657, c290, c668, c106, c669, c671, c45, c296, c297, c672, c333, c331, c629, c272, c41, c23, c64, c209, c345, c343, c206, c217] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c668 := derived668 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c669 := derived669 a h
  have h9 : Entails.eval a c671 := derived671 a h
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c296 := h 295 (by decide)
  have h12 : Entails.eval a c297 := h 296 (by decide)
  have h13 : Entails.eval a c672 := derived672 a h
  have h14 : Entails.eval a c333 := h 332 (by decide)
  have h15 : Entails.eval a c331 := h 330 (by decide)
  have h16 : Entails.eval a c629 := derived629 a h
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c41 := h 40 (by decide)
  have h19 : Entails.eval a c23 := h 22 (by decide)
  have h20 : Entails.eval a c64 := h 63 (by decide)
  have h21 : Entails.eval a c209 := h 208 (by decide)
  have h22 : Entails.eval a c345 := h 344 (by decide)
  have h23 : Entails.eval a c343 := h 342 (by decide)
  have h24 : Entails.eval a c206 := h 205 (by decide)
  have h25 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c50, some c104, some c103, some c88, some c606, some c377, some c292, some c547, some c45, some c301, some c296, some c576, some c647, some c610, some c339, some c343, some c22, some c19, some c197, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c667, c543, c613, c379, c657, c290, c50, c104, c103, c88, c606, c377, c292, c547, c45, c301, c296, c576, c647, c610, c339, c343, c22, c19, c197] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c606 := derived606 a h
  have h11 : Entails.eval a c377 := h 376 (by decide)
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c547 := derived547 a h
  have h14 : Entails.eval a c45 := h 44 (by decide)
  have h15 : Entails.eval a c301 := h 300 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c576 := derived576 a h
  have h18 : Entails.eval a c647 := derived647 a h
  have h19 : Entails.eval a c610 := derived610 a h
  have h20 : Entails.eval a c339 := h 338 (by decide)
  have h21 : Entails.eval a c343 := h 342 (by decide)
  have h22 : Entails.eval a c22 := h 21 (by decide)
  have h23 : Entails.eval a c19 := h 18 (by decide)
  have h24 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c306, some c55, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c301, c306, c55] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c306 := h 305 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c657, some c613, some c379, some c290, some c674, some c673, some c675, some c292, some c667, some c55, some c44, some c302, some c340, some c270, some c269, some c333, some c346, some c63, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c543, c657, c613, c379, c290, c674, c673, c675, c292, c667, c55, c44, c302, c340, c270, c269, c333, c346, c63] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c657 := derived657 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c674 := derived674 a h
  have h6 : Entails.eval a c673 := derived673 a h
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c292 := h 291 (by decide)
  have h9 : Entails.eval a c667 := derived667 a h
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c302 := h 301 (by decide)
  have h13 : Entails.eval a c340 := h 339 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c346 := h 345 (by decide)
  have h18 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c674, some c673, some c675, some c292, some c676, some c297, some c45, some c53, some c37, some c302, some c328, some c327, some c65, some c270, some c331, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c667, c543, c613, c379, c657, c290, c674, c673, c675, c292, c676, c297, c45, c53, c37, c302, c328, c327, c65, c270, c331] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c674 := derived674 a h
  have h7 : Entails.eval a c673 := derived673 a h
  have h8 : Entails.eval a c675 := derived675 a h
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c676 := derived676 a h
  have h11 : Entails.eval a c297 := h 296 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c328 := h 327 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c65 := h 64 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c657, some c613, some c379, some c290, some c675, some c292, some c667, some c45, some c53, some c37, some c302, some c328, some c327, some c65, some c270, some c331, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c543, c657, c613, c379, c290, c675, c292, c667, c45, c53, c37, c302, c328, c327, c65, c270, c331] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c657 := derived657 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c675 := derived675 a h
  have h6 : Entails.eval a c292 := h 291 (by decide)
  have h7 : Entails.eval a c667 := derived667 a h
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c328 := h 327 (by decide)
  have h13 : Entails.eval a c327 := h 326 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c270 := h 269 (by decide)
  have h16 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c543, some c613, some c379, some c657, some c290, some c675, some c292, some c678, some c296, some c297, some c44, some c340, some c270, some c269, some c333, some c346, some c63, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c667, c543, c613, c379, c657, c290, c675, c292, c678, c296, c297, c44, c340, c270, c269, c333, c346, c63] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c543 := derived543 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c675 := derived675 a h
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c678 := derived678 a h
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c340 := h 339 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c333 := h 332 (by decide)
  have h16 : Entails.eval a c346 := h 345 (by decide)
  have h17 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c677, some c679, some c105, some c667, some c543, some c613, some c379, some c657, some c290, some c292, some c566, some c41, some c54, some c331, some c296, some c297, some c63, some c271, some c272, some c346, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c677, c679, c105, c667, c543, c613, c379, c657, c290, c292, c566, c41, c54, c331, c296, c297, c63, c271, c272, c346] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c677 := derived677 a h
  have h1 : Entails.eval a c679 := derived679 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c667 := derived667 a h
  have h4 : Entails.eval a c543 := derived543 a h
  have h5 : Entails.eval a c613 := derived613 a h
  have h6 : Entails.eval a c379 := h 378 (by decide)
  have h7 : Entails.eval a c657 := derived657 a h
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c566 := derived566 a h
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c331 := h 330 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  have h15 : Entails.eval a c297 := h 296 (by decide)
  have h16 : Entails.eval a c63 := h 62 (by decide)
  have h17 : Entails.eval a c271 := h 270 (by decide)
  have h18 : Entails.eval a c272 := h 271 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c290, some c667, some c680, some c301, some c53, some c296, some c38, some c333, some c43, some c677, some c139, some c12, some c306, some c272, some c679, some c105, some c328, some c343, some c86, some c109, some c331, some c206, some c23, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c543, c613, c379, c657, c290, c667, c680, c301, c53, c296, c38, c333, c43, c677, c139, c12, c306, c272, c679, c105, c328, c343, c86, c109, c331, c206, c23] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c680 := derived680 a h
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c333 := h 332 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c677 := derived677 a h
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c12 := h 11 (by decide)
  have h16 : Entails.eval a c306 := h 305 (by decide)
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c679 := derived679 a h
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c343 := h 342 (by decide)
  have h22 : Entails.eval a c86 := h 85 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c331 := h 330 (by decide)
  have h25 : Entails.eval a c206 := h 205 (by decide)
  have h26 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c677, some c667, some c543, some c613, some c379, some c657, some c290, some c679, some c105, some c680, some c301, some c306, some c38, some c53, some c333, some c296, some c43, some c139, some c272, some c12, some c681, some c19, some c64, some c196, some c352, some c109, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c677, c667, c543, c613, c379, c657, c290, c679, c105, c680, c301, c306, c38, c53, c333, c296, c43, c139, c272, c12, c681, c19, c64, c196, c352, c109] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c677 := derived677 a h
  have h1 : Entails.eval a c667 := derived667 a h
  have h2 : Entails.eval a c543 := derived543 a h
  have h3 : Entails.eval a c613 := derived613 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c657 := derived657 a h
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c679 := derived679 a h
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c680 := derived680 a h
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c306 := h 305 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c333 := h 332 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c139 := h 138 (by decide)
  have h18 : Entails.eval a c272 := h 271 (by decide)
  have h19 : Entails.eval a c12 := h 11 (by decide)
  have h20 : Entails.eval a c681 := derived681 a h
  have h21 : Entails.eval a c19 := h 18 (by decide)
  have h22 : Entails.eval a c64 := h 63 (by decide)
  have h23 : Entails.eval a c196 := h 195 (by decide)
  have h24 : Entails.eval a c352 := h 351 (by decide)
  have h25 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c677, some c682, some c100, some c543, some c657, some c50, some c103, some c104, some c667, some c613, some c379, some c290, some c301, some c306, some c576, some c577, some c590, some c206, some c333, some c134, some c9, some c6, some c138, some c109, some c346, some c352, some c64, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c677, c682, c100, c543, c657, c50, c103, c104, c667, c613, c379, c290, c301, c306, c576, c577, c590, c206, c333, c134, c9, c6, c138, c109, c346, c352, c64] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c677 := derived677 a h
  have h1 : Entails.eval a c682 := derived682 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c543 := derived543 a h
  have h4 : Entails.eval a c657 := derived657 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c667 := derived667 a h
  have h9 : Entails.eval a c613 := derived613 a h
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c576 := derived576 a h
  have h15 : Entails.eval a c577 := derived577 a h
  have h16 : Entails.eval a c590 := derived590 a h
  have h17 : Entails.eval a c206 := h 205 (by decide)
  have h18 : Entails.eval a c333 := h 332 (by decide)
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c9 := h 8 (by decide)
  have h21 : Entails.eval a c6 := h 5 (by decide)
  have h22 : Entails.eval a c138 := h 137 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c346 := h 345 (by decide)
  have h25 : Entails.eval a c352 := h 351 (by decide)
  have h26 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c543, some c613, some c379, some c657, some c50, some c290, some c667, some c677, some c682, some c104, some c100, some c683, some c54, some c60, some c296, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c543, c613, c379, c657, c50, c290, c667, c677, c682, c104, c100, c683, c54, c60, c296] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c543 := derived543 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c379 := h 378 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c667 := derived667 a h
  have h7 : Entails.eval a c677 := derived677 a h
  have h8 : Entails.eval a c682 := derived682 a h
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c683 := derived683 a h
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived684

end CochromaticTwenty.Certificates.B16_4_1
