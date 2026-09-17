import MerLeanExperiment.Certificates.B16_3_1.Steps0100_0199

/-! Generated from the actual pinned b16_3_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_3_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c581 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c580, some c575, some c546, some c69, some c70, some c340, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c580, c575, c546, c69, c70, c340] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c580 := derived580 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨43, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c561, some c575, some c581, some c335, some c330, some c580, some c546, some c350, some c308, some c88, some c87, some c393, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c497, c561, c575, c581, c335, c330, c580, c546, c350, c308, c88, c87, c393] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c561 := derived561 a h
  have h2 : Entails.eval a c575 := derived575 a h
  have h3 : Entails.eval a c581 := derived581 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c580 := derived580 a h
  have h7 : Entails.eval a c546 := derived546 a h
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c308 := h 307 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c393 := derived393 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨43, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c546, some c582, some c370, some c379, some c98, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c546, c582, c370, c379, c98] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c546 := derived546 a h
  have h1 : Entails.eval a c582 := derived582 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c546, some c61, some c336, some c335, some c580, some c97, some c79, some c583, some c497, some c379, some c332, some c340, some c71, some c44, some c117, some c118, some c283, some c19, some c54, some c90, some c198, some c263, some c17, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c575, c546, c61, c336, c335, c580, c97, c79, c583, c497, c379, c332, c340, c71, c44, c117, c118, c283, c19, c54, c90, c198, c263, c17] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c336 := h 335 (by decide)
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c580 := derived580 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c583 := derived583 a h
  have h9 : Entails.eval a c497 := derived497 a h
  have h10 : Entails.eval a c379 := h 378 (by decide)
  have h11 : Entails.eval a c332 := h 331 (by decide)
  have h12 : Entails.eval a c340 := h 339 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c19 := h 18 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c90 := h 89 (by decide)
  have h21 : Entails.eval a c198 := h 197 (by decide)
  have h22 : Entails.eval a c263 := h 262 (by decide)
  have h23 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c580, some c575, some c546, some c497, some c79, some c61, some c335, some c336, some c584, some c489, some c117, some c71, some c340, some c332, some c380, some c330, some c350, some c308, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c583, c580, c575, c546, c497, c79, c61, c335, c336, c584, c489, c117, c71, c340, c332, c380, c330, c350, c308] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c580 := derived580 a h
  have h2 : Entails.eval a c575 := derived575 a h
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c497 := derived497 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c335 := h 334 (by decide)
  have h8 : Entails.eval a c336 := h 335 (by decide)
  have h9 : Entails.eval a c584 := derived584 a h
  have h10 : Entails.eval a c489 := derived489 a h
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c340 := h 339 (by decide)
  have h14 : Entails.eval a c332 := h 331 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c330 := h 329 (by decide)
  have h17 : Entails.eval a c350 := h 349 (by decide)
  have h18 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨43, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c585, some c370, some c81, some c117, some c372, some c350, some c580, some c575, some c546, some c497, some c335, some c336, some c330, some c71, some c308, some c313, some c87, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c583, c585, c370, c81, c117, c372, c350, c580, c575, c546, c497, c335, c336, c330, c71, c308, c313, c87] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c585 := derived585 a h
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c372 := h 371 (by decide)
  have h6 : Entails.eval a c350 := h 349 (by decide)
  have h7 : Entails.eval a c580 := derived580 a h
  have h8 : Entails.eval a c575 := derived575 a h
  have h9 : Entails.eval a c546 := derived546 a h
  have h10 : Entails.eval a c497 := derived497 a h
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c330 := h 329 (by decide)
  have h14 : Entails.eval a c71 := h 70 (by decide)
  have h15 : Entails.eval a c308 := h 307 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c580, some c575, some c546, some c497, some c583, some c585, some c370, some c372, some c81, some c350, some c117, some c586, some c43, some c69, some c282, some c341, some c50, some c330, some c322, some c566, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c580, c575, c546, c497, c583, c585, c370, c372, c81, c350, c117, c586, c43, c69, c282, c341, c50, c330, c322, c566] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c580 := derived580 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c546 := derived546 a h
  have h3 : Entails.eval a c497 := derived497 a h
  have h4 : Entails.eval a c583 := derived583 a h
  have h5 : Entails.eval a c585 := derived585 a h
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c586 := derived586 a h
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c282 := h 281 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c330 := h 329 (by decide)
  have h18 : Entails.eval a c322 := h 321 (by decide)
  have h19 : Entails.eval a c566 := derived566 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c587, some c580, some c575, some c546, some c497, some c61, some c69, some c370, some c372, some c341, some c312, some c330, some c87, some c357, some c358, some c489, some c352, some c566, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c587, c580, c575, c546, c497, c61, c69, c370, c372, c341, c312, c330, c87, c357, c358, c489, c352, c566] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c587 := derived587 a h
  have h1 : Entails.eval a c580 := derived580 a h
  have h2 : Entails.eval a c575 := derived575 a h
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c497 := derived497 a h
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c341 := h 340 (by decide)
  have h10 : Entails.eval a c312 := h 311 (by decide)
  have h11 : Entails.eval a c330 := h 329 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c358 := h 357 (by decide)
  have h15 : Entails.eval a c489 := derived489 a h
  have h16 : Entails.eval a c352 := h 351 (by decide)
  have h17 : Entails.eval a c566 := derived566 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c497, some c546, some c575, some c580, some c587, some c588, some c335, some c336, some c307, some c79, some c25, some c87, some c372, some c230, some c198, some c363, some c362, some c312, some c330, some c352, some c88, some c71, some c199, some c557, some c118, some c36, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c497, c546, c575, c580, c587, c588, c335, c336, c307, c79, c25, c87, c372, c230, c198, c363, c362, c312, c330, c352, c88, c71, c199, c557, c118, c36] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c497 := derived497 a h
  have h1 : Entails.eval a c546 := derived546 a h
  have h2 : Entails.eval a c575 := derived575 a h
  have h3 : Entails.eval a c580 := derived580 a h
  have h4 : Entails.eval a c587 := derived587 a h
  have h5 : Entails.eval a c588 := derived588 a h
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c362 := h 361 (by decide)
  have h17 : Entails.eval a c312 := h 311 (by decide)
  have h18 : Entails.eval a c330 := h 329 (by decide)
  have h19 : Entails.eval a c352 := h 351 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c71 := h 70 (by decide)
  have h22 : Entails.eval a c199 := h 198 (by decide)
  have h23 : Entails.eval a c557 := derived557 a h
  have h24 : Entails.eval a c118 := h 117 (by decide)
  have h25 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c335, some c336, some c307, some c334, some c79, some c25, some c87, some c373, some c229, some c363, some c365, some c333, some c130, some c31, some c84, some c200, some c16, some c129, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c589, c335, c336, c307, c334, c79, c25, c87, c373, c229, c363, c365, c333, c130, c31, c84, c200, c16, c129] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c335 := h 334 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c307 := h 306 (by decide)
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c229 := h 228 (by decide)
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c365 := h 364 (by decide)
  have h12 : Entails.eval a c333 := h 332 (by decide)
  have h13 : Entails.eval a c130 := h 129 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c200 := h 199 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c590, some c373, some c329, some c25, some c87, some c229, some c200, some c363, some c365, some c130, some c129, some c31, some c84, some c16, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c369, c590, c373, c329, c25, c87, c229, c200, c363, c365, c130, c129, c31, c84, c16] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c373 := h 372 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c229 := h 228 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c130 := h 129 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c84 := h 83 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c373, some c591, some c358, some c359, some c355, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c589, c373, c591, c358, c359, c355] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨44, by decide⟩, false), (⟨1, by decide⟩, true), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c592, some c79, some c97, some c358, some c359, some c378, some c355, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c589, c592, c79, c97, c358, c359, c378, c355] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨55, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c357, some c358, some c356, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c589, c357, c358, c356] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨54, by decide⟩, true), (⟨53, by decide⟩, false), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c376, some c329, some c328, some c337, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c374, c376, c329, c328, c337] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c328 := h 327 (by decide)
  have h4 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c467, some c99, some c117, some c118, some c72, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c589, c467, c99, c117, c118, c72] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c467 := derived467 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c590, some c593, some c594, some c87, some c363, some c362, some c88, some c354, some c596, some c374, some c376, some c63, some c328, some c117, some c338, some c68, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c589, c590, c593, c594, c87, c363, c362, c88, c354, c596, c374, c376, c63, c328, c117, c338, c68] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c593 := derived593 a h
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c362 := h 361 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c354 := h 353 (by decide)
  have h9 : Entails.eval a c596 := derived596 a h
  have h10 : Entails.eval a c374 := h 373 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c328 := h 327 (by decide)
  have h14 : Entails.eval a c117 := h 116 (by decide)
  have h15 : Entails.eval a c338 := h 337 (by decide)
  have h16 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨44, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c377, some c594, some c352, some c87, some c363, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c378, c377, c594, c352, c87, c363] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c377 := h 376 (by decide)
  have h2 : Entails.eval a c594 := derived594 a h
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨53, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨44, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c25, some c87, some c363, some c362, some c88, some c354, some c375, some c229, some c63, some c221, some c223, some c117, some c246, some c250, some c35, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c79, c25, c87, c363, c362, c88, c354, c375, c229, c63, c221, c223, c117, c246, c250, c35] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c363 := h 362 (by decide)
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c223 := h 222 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c246 := h 245 (by decide)
  have h14 : Entails.eval a c250 := h 249 (by decide)
  have h15 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c597, some c598, some c595, some c599, some c358, some c594, some c355, some c375, some c309, some c329, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c589, c597, c598, c595, c599, c358, c594, c355, c375, c309, c329] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c597 := derived597 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c599 := derived599 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c594 := derived594 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c309 := h 308 (by decide)
  have h10 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c597, some c598, some c600, some c335, some c336, some c307, some c334, some c68, some c333, some c79, some c25, some c87, some c337, some c229, some c363, some c362, some c221, some c88, some c227, some c118, some c64, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c589, c597, c598, c600, c335, c336, c307, c334, c68, c333, c79, c25, c87, c337, c229, c363, c362, c221, c88, c227, c118, c64] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c597 := derived597 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c335 := h 334 (by decide)
  have h5 : Entails.eval a c336 := h 335 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c334 := h 333 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c25 := h 24 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c337 := h 336 (by decide)
  have h14 : Entails.eval a c229 := h 228 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c362 := h 361 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c88 := h 87 (by decide)
  have h19 : Entails.eval a c227 := h 226 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨8, by decide⟩, false), (⟨44, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c88, some c117, some c118, some c72, some c28, some c199, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c25, c88, c117, c118, c72, c28, c199] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c597, some c601, some c97, some c62, some c80, some c99, some c362, some c312, some c602, some c358, some c594, some c373, some c369, some c355, some c329, some c309, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c589, c597, c601, c97, c62, c80, c99, c362, c312, c602, c358, c594, c373, c369, c355, c329, c309] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c597 := derived597 a h
  have h2 : Entails.eval a c601 := derived601 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c602 := derived602 a h
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c594 := derived594 a h
  have h12 : Entails.eval a c373 := h 372 (by decide)
  have h13 : Entails.eval a c369 := h 368 (by decide)
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  have h16 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨42, by decide⟩, false), (⟨34, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c312, some c358, some c594, some c373, some c369, some c355, some c329, some c315, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c589, c312, c358, c594, c373, c369, c355, c329, c315] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c312 := h 311 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c603, some c69, some c43, some c61, some c80, some c99, some c362, some c312, some c604, some c88, some c117, some c63, some c45, some c278, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c589, c603, c69, c43, c61, c80, c99, c362, c312, c604, c88, c117, c63, c45, c278] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c604 := derived604 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨44, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c605, some c598, some c603, some c69, some c87, some c312, some c599, some c374, some c376, some c329, some c328, some c343, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c605, c598, c603, c69, c87, c312, c599, c374, c376, c329, c328, c343] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c605 := derived605 a h
  have h1 : Entails.eval a c598 := derived598 a h
  have h2 : Entails.eval a c603 := derived603 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c312 := h 311 (by decide)
  have h6 : Entails.eval a c599 := derived599 a h
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c328 := h 327 (by decide)
  have h11 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c605, some c603, some c69, some c61, some c606, some c357, some c358, some c594, some c604, some c86, some c375, some c26, some c489, some c234, some c117, some c221, some c225, some c250, some c246, some c34, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c589, c605, c603, c69, c61, c606, c357, c358, c594, c604, c86, c375, c26, c489, c234, c117, c221, c225, c250, c246, c34] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c605 := derived605 a h
  have h2 : Entails.eval a c603 := derived603 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c606 := derived606 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c594 := derived594 a h
  have h9 : Entails.eval a c604 := derived604 a h
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c375 := h 374 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c489 := derived489 a h
  have h14 : Entails.eval a c234 := h 233 (by decide)
  have h15 : Entails.eval a c117 := h 116 (by decide)
  have h16 : Entails.eval a c221 := h 220 (by decide)
  have h17 : Entails.eval a c225 := h 224 (by decide)
  have h18 : Entails.eval a c250 := h 249 (by decide)
  have h19 : Entails.eval a c246 := h 245 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c358, some c359, some c594, some c355, some c378, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c589, c358, c359, c594, c355, c378] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨36, by decide⟩, true), (⟨46, by decide⟩, true), (⟨35, by decide⟩, true), (⟨45, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c378, some c328, some c353, some c376, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c375, c378, c328, c353, c376] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c603, some c69, some c605, some c607, some c608, some c87, some c363, some c362, some c312, some c365, some c313, some c609, some c354, some c374, some c376, some c328, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c603, c69, c605, c607, c608, c87, c363, c362, c312, c365, c313, c609, c354, c374, c376, c328] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c605 := derived605 a h
  have h3 : Entails.eval a c607 := derived607 a h
  have h4 : Entails.eval a c608 := derived608 a h
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c312 := h 311 (by decide)
  have h9 : Entails.eval a c365 := h 364 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c609 := derived609 a h
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c374 := h 373 (by decide)
  have h14 : Entails.eval a c376 := h 375 (by decide)
  have h15 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨55, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c610, some c363, some c362, some c85, some c88, some c354, some c113, some c114, some c374, some c376, some c100, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c610, c363, c362, c85, c88, c354, c113, c114, c374, c376, c100] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c610 := derived610 a h
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c374 := h 373 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c228, some c129, some c30, some c9, some c170, some c158, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c228, c129, c30, c9, c170, c158] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c228 := h 227 (by decide)
  have h1 : Entails.eval a c129 := h 128 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c9 := h 8 (by decide)
  have h4 : Entails.eval a c170 := h 169 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨42, by decide⟩, true), (⟨55, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c612, some c355, some c84, some c367, some c115, some c116, some c353, some c102, some c376, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c589, c612, c355, c84, c367, c115, c116, c353, c102, c376] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c612 := derived612 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c367 := h 366 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨55, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c67, some c85, some c102, some c318, some c227, some c63, some c36, some c226, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c67, c85, c102, c318, c227, c63, c36, c226] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c67 := h 66 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c227 := h 226 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨44, by decide⟩, false), (⟨2, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c114, some c614, some c116, some c101, some c66, some c226, some c321, some c36, some c64, some c227, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c112, c114, c614, c116, c101, c66, c226, c321, c36, c64, c227] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c614 := derived614 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨47, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c66, some c498, some c376, some c321, some c330, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c103, c66, c498, c376, c321, c330] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c498 := derived498 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c321 := h 320 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c610, some c608, some c79, some c25, some c611, some c613, some c615, some c88, some c367, some c356, some c616, some c115, some c116, some c104, some c102, some c376, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c589, c610, c608, c79, c25, c611, c613, c615, c88, c367, c356, c616, c115, c116, c104, c102, c376] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c610 := derived610 a h
  have h2 : Entails.eval a c608 := derived608 a h
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c613 := derived613 a h
  have h7 : Entails.eval a c615 := derived615 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c616 := derived616 a h
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c116 := h 115 (by decide)
  have h14 : Entails.eval a c104 := h 103 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c116, some c102, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c115, c116, c102] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨33, by decide⟩, false), (⟨28, by decide⟩, true), (⟨52, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c64, some c20, some c199, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c64, c20, c199] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨33, by decide⟩, false), (⟨6, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c337, some c320, some c75, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c337, c320, c75] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c337 := h 336 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c608, some c25, some c79, some c610, some c611, some c613, some c617, some c377, some c228, some c618, some c22, some c280, some c274, some c43, some c619, some c114, some c88, some c52, some c367, some c270, some c356, some c620, some c330, some c258, some c318, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c589, c608, c25, c79, c610, c611, c613, c617, c377, c228, c618, c22, c280, c274, c43, c619, c114, c88, c52, c367, c270, c356, c620, c330, c258, c318] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c608 := derived608 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c610 := derived610 a h
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c613 := derived613 a h
  have h7 : Entails.eval a c617 := derived617 a h
  have h8 : Entails.eval a c377 := h 376 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  have h10 : Entails.eval a c618 := derived618 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c274 := h 273 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  have h15 : Entails.eval a c619 := derived619 a h
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c52 := h 51 (by decide)
  have h19 : Entails.eval a c367 := h 366 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c356 := h 355 (by decide)
  have h22 : Entails.eval a c620 := derived620 a h
  have h23 : Entails.eval a c330 := h 329 (by decide)
  have h24 : Entails.eval a c258 := h 257 (by decide)
  have h25 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨45, by decide⟩, false), (⟨47, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨44, by decide⟩, false), (⟨2, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c367, some c355, some c66, some c101, some c498, some c321, some c394, some c328, some c317, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c589, c367, c355, c66, c101, c498, c321, c394, c328, c317] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c498 := derived498 a h
  have h6 : Entails.eval a c321 := h 320 (by decide)
  have h7 : Entails.eval a c394 := derived394 a h
  have h8 : Entails.eval a c328 := h 327 (by decide)
  have h9 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨55, by decide⟩, false), (⟨41, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c79, some c229, some c610, some c486, some c579, some c88, some c622, some c115, some c116, some c64, some c38, some c320, some c199, some c70, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c25, c79, c229, c610, c486, c579, c88, c622, c115, c116, c64, c38, c320, c199, c70] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c610 := derived610 a h
  have h4 : Entails.eval a c486 := derived486 a h
  have h5 : Entails.eval a c579 := derived579 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c622 := derived622 a h
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c116 := h 115 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c116, some c101, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c113, c116, c101] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c610, some c608, some c79, some c25, some c621, some c375, some c378, some c229, some c623, some c376, some c227, some c624, some c38, some c115, some c114, some c103, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c610, c608, c79, c25, c621, c375, c378, c229, c623, c376, c227, c624, c38, c115, c114, c103] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c610 := derived610 a h
  have h1 : Entails.eval a c608 := derived608 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c621 := derived621 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c623 := derived623 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c624 := derived624 a h
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c610, some c114, some c115, some c375, some c378, some c624, some c66, some c84, some c103, some c470, some c376, some c486, some c357, some c498, some c88, some c76, some c49, some c317, some c281, some c595, some c43, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c610, c114, c115, c375, c378, c624, c66, c84, c103, c470, c376, c486, c357, c498, c88, c76, c49, c317, c281, c595, c43] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c610 := derived610 a h
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c624 := derived624 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c470 := derived470 a h
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c486 := derived486 a h
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c498 := derived498 a h
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c317 := h 316 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c595 := derived595 a h
  have h20 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨47, by decide⟩, false), (⟨55, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c498, some c374, some c67, some c624, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c103, c498, c374, c67, c624] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c498 := derived498 a h
  have h2 : Entails.eval a c374 := h 373 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c624 := derived624 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨33, by decide⟩, false), (⟨22, by decide⟩, true), (⟨17, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c45, some c198, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c37, c45, c198] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c610, some c115, some c114, some c626, some c594, some c611, some c79, some c25, some c88, some c613, some c367, some c356, some c627, some c228, some c22, some c280, some c277, some c43, some c52, some c270, some c628, some c113, some c67, some c23, some c201, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c589, c610, c115, c114, c626, c594, c611, c79, c25, c88, c613, c367, c356, c627, c228, c22, c280, c277, c43, c52, c270, c628, c113, c67, c23, c201] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c610 := derived610 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c626 := derived626 a h
  have h5 : Entails.eval a c594 := derived594 a h
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c613 := derived613 a h
  have h11 : Entails.eval a c367 := h 366 (by decide)
  have h12 : Entails.eval a c356 := h 355 (by decide)
  have h13 : Entails.eval a c627 := derived627 a h
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c280 := h 279 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c52 := h 51 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c628 := derived628 a h
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c67 := h 66 (by decide)
  have h24 : Entails.eval a c23 := h 22 (by decide)
  have h25 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c625, some c629, some c82, some c376, some c377, some c28, some c105, some c66, some c84, some c103, some c117, some c470, some c101, some c227, some c369, some c25, some c594, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c589, c625, c629, c82, c376, c377, c28, c105, c66, c84, c103, c117, c470, c101, c227, c369, c25, c594] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c625 := derived625 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c470 := derived470 a h
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c227 := h 226 (by decide)
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c594 := derived594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c610, some c625, some c629, some c28, some c82, some c232, some c630, some c116, some c92, some c363, some c357, some c216, some c79, some c227, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c610, c625, c629, c28, c82, c232, c630, c116, c92, c363, c357, c216, c79, c227] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c610 := derived610 a h
  have h1 : Entails.eval a c625 := derived625 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c630 := derived630 a h
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨41, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c79, some c227, some c38, some c20, some c229, some c279, some c67, some c43, some c201, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c25, c79, c227, c38, c20, c229, c279, c67, c43, c201] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c227 := h 226 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c229 := h 228 (by decide)
  have h6 : Entails.eval a c279 := h 278 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c610, some c116, some c115, some c79, some c632, some c82, some c618, some c373, some c369, some c623, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c610, c116, c115, c79, c632, c82, c618, c373, c369, c623] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c610 := derived610 a h
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c632 := derived632 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c618 := derived618 a h
  have h7 : Entails.eval a c373 := h 372 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c623 := derived623 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c631, some c610, some c115, some c116, some c633, some c357, some c358, some c594, some c92, some c349, some c359, some c362, some c355, some c94, some c373, some c112, some c61, some c307, some c308, some c72, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c589, c631, c610, c115, c116, c633, c357, c358, c594, c92, c349, c359, c362, c355, c94, c373, c112, c61, c307, c308, c72] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c610 := derived610 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c633 := derived633 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c594 := derived594 a h
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c349 := h 348 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c373 := h 372 (by decide)
  have h16 : Entails.eval a c112 := h 111 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  have h18 : Entails.eval a c307 := h 306 (by decide)
  have h19 : Entails.eval a c308 := h 307 (by decide)
  have h20 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c94, some c308, some c112, some c72, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c92, c94, c308, c112, c72] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c308 := h 307 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨45, by decide⟩, true), (⟨47, by decide⟩, true), (⟨41, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c635, some c113, some c72, some c73, some c337, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c635, c113, c72, c73, c337] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c635 := derived635 a h
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c72 := h 71 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c631, some c358, some c349, some c362, some c357, some c634, some c610, some c61, some c307, some c636, some c114, some c94, some c93, some c113, some c470, some c73, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c589, c631, c358, c349, c362, c357, c634, c610, c61, c307, c636, c114, c94, c93, c113, c470, c73] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c362 := h 361 (by decide)
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c634 := derived634 a h
  have h7 : Entails.eval a c610 := derived610 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c636 := derived636 a h
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c93 := h 92 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c470 := derived470 a h
  have h16 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c634, some c631, some c610, some c357, some c358, some c594, some c349, some c362, some c637, some c373, some c369, some c101, some c624, some c112, some c94, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c589, c634, c631, c610, c357, c358, c594, c349, c362, c637, c373, c369, c101, c624, c112, c94] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c634 := derived634 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c610 := derived610 a h
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c594 := derived594 a h
  have h7 : Entails.eval a c349 := h 348 (by decide)
  have h8 : Entails.eval a c362 := h 361 (by decide)
  have h9 : Entails.eval a c637 := derived637 a h
  have h10 : Entails.eval a c373 := h 372 (by decide)
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c624 := derived624 a h
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c31, some c229, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c85, c31, c229] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c638, some c25, some c79, some c631, some c610, some c639, some c363, some c349, some c367, some c88, some c112, some c114, some c614, some c632, some c369, some c579, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c589, c638, c25, c79, c631, c610, c639, c363, c349, c367, c88, c112, c114, c614, c632, c369, c579] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c610 := derived610 a h
  have h6 : Entails.eval a c639 := derived639 a h
  have h7 : Entails.eval a c363 := h 362 (by decide)
  have h8 : Entails.eval a c349 := h 348 (by decide)
  have h9 : Entails.eval a c367 := h 366 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c614 := derived614 a h
  have h14 : Entails.eval a c632 := derived632 a h
  have h15 : Entails.eval a c369 := h 368 (by decide)
  have h16 : Entails.eval a c579 := derived579 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c373, some c369, some c101, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c373, c369, c101] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c373 := h 372 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c579, some c371, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c101, c579, c371] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c579 := derived579 a h
  have h2 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c642, some c226, some c36, some c37, some c245, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c114, c642, c226, c36, c37, c245] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c642 := derived642 a h
  have h2 : Entails.eval a c226 := h 225 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c610, some c631, some c634, some c638, some c79, some c25, some c640, some c113, some c643, some c88, some c362, some c367, some c349, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c589, c610, c631, c634, c638, c79, c25, c640, c113, c643, c88, c362, c367, c349] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c610 := derived610 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c634 := derived634 a h
  have h4 : Entails.eval a c638 := derived638 a h
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c640 := derived640 a h
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c643 := derived643 a h
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c362 := h 361 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c81, some c27, some c226, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c81, c27, c226] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨51, by decide⟩, false), (⟨42, by decide⟩, false), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c226, some c369, some c219, some c227, some c245, some c352, some c220, some c366, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c226, c369, c219, c227, c245, c352, c220, c366] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c226 := h 225 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c227 := h 226 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c644, some c79, some c25, some c645, some c226, some c127, some c168, some c646, some c364, some c159, some c88, some c11, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c644, c79, c25, c645, c226, c127, c168, c646, c364, c159, c88, c11] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c226 := h 225 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c646 := derived646 a h
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c507, some c366, some c228, some c220, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c507, c366, c228, c220] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c507 := derived507 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨7, by decide⟩, false), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c645, some c127, some c12, some c648, some c130, some c247, some c220, some c365, some c350, some c219, some c227, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c645, c127, c12, c648, c130, c247, c220, c365, c350, c219, c227] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c645 := derived645 a h
  have h1 : Entails.eval a c127 := h 126 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c648 := derived648 a h
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c247 := h 246 (by decide)
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨23, by decide⟩, true), (⟨51, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c221, some c227, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c350, c221, c227] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨22, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨7, by decide⟩, false), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c243, some c130, some c650, some c365, some c30, some c129, some c16, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c649, c243, c130, c650, c365, c30, c129, c16] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c650 := derived650 a h
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨7, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c644, some c79, some c645, some c113, some c87, some c647, some c649, some c244, some c651, some c507, some c366, some c371, some c393, some c88, some c222, some c117, some c248, some c35, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c25, c644, c79, c645, c113, c87, c647, c649, c244, c651, c507, c366, c371, c393, c88, c222, c117, c248, c35] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c79 := h 78 (by decide)
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c647 := derived647 a h
  have h7 : Entails.eval a c649 := derived649 a h
  have h8 : Entails.eval a c244 := h 243 (by decide)
  have h9 : Entails.eval a c651 := derived651 a h
  have h10 : Entails.eval a c507 := derived507 a h
  have h11 : Entails.eval a c366 := h 365 (by decide)
  have h12 : Entails.eval a c371 := h 370 (by decide)
  have h13 : Entails.eval a c393 := derived393 a h
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c222 := h 221 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c644, some c79, some c25, some c645, some c113, some c87, some c647, some c649, some c243, some c652, some c228, some c351, some c507, some c365, some c650, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c644, c79, c25, c645, c113, c87, c647, c649, c243, c652, c228, c351, c507, c365, c650] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c647 := derived647 a h
  have h7 : Entails.eval a c649 := derived649 a h
  have h8 : Entails.eval a c243 := h 242 (by decide)
  have h9 : Entails.eval a c652 := derived652 a h
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c351 := h 350 (by decide)
  have h12 : Entails.eval a c507 := derived507 a h
  have h13 : Entails.eval a c365 := h 364 (by decide)
  have h14 : Entails.eval a c650 := derived650 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c79, some c25, some c653, some c639, some c644, some c645, some c507, some c373, some c371, some c106, some c393, some c117, some c88, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c589, c79, c25, c653, c639, c644, c645, c507, c373, c371, c106, c393, c117, c88] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c653 := derived653 a h
  have h4 : Entails.eval a c639 := derived639 a h
  have h5 : Entails.eval a c644 := derived644 a h
  have h6 : Entails.eval a c645 := derived645 a h
  have h7 : Entails.eval a c507 := derived507 a h
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c393 := derived393 a h
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨42, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c87, some c79, some c25, some c653, some c639, some c373, some c371, some c612, some c228, some c67, some c618, some c22, some c280, some c277, some c43, some c23, some c201, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c87, c79, c25, c653, c639, c373, c371, c612, c228, c67, c618, c22, c280, c277, c43, c23, c201] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c87 := h 86 (by decide)
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c653 := derived653 a h
  have h4 : Entails.eval a c639 := derived639 a h
  have h5 : Entails.eval a c373 := h 372 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  have h7 : Entails.eval a c612 := derived612 a h
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c618 := derived618 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c277 := h 276 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  have h15 : Entails.eval a c23 := h 22 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, true), (⟨54, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨47, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c627, some c618, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c627, c618] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c618 := derived618 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c644, some c654, some c655, some c351, some c79, some c25, some c645, some c87, some c112, some c88, some c653, some c639, some c350, some c368, some c349, some c656, some c229, some c23, some c281, some c277, some c43, some c52, some c273, some c619, some c115, some c22, some c66, some c200, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c589, c644, c654, c655, c351, c79, c25, c645, c87, c112, c88, c653, c639, c350, c368, c349, c656, c229, c23, c281, c277, c43, c52, c273, c619, c115, c22, c66, c200] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c654 := derived654 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c645 := derived645 a h
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c653 := derived653 a h
  have h12 : Entails.eval a c639 := derived639 a h
  have h13 : Entails.eval a c350 := h 349 (by decide)
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c656 := derived656 a h
  have h17 : Entails.eval a c229 := h 228 (by decide)
  have h18 : Entails.eval a c23 := h 22 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  have h20 : Entails.eval a c277 := h 276 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c52 := h 51 (by decide)
  have h23 : Entails.eval a c273 := h 272 (by decide)
  have h24 : Entails.eval a c619 := derived619 a h
  have h25 : Entails.eval a c115 := h 114 (by decide)
  have h26 : Entails.eval a c22 := h 21 (by decide)
  have h27 : Entails.eval a c66 := h 65 (by decide)
  have h28 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c25, some c653, some c639, some c644, some c654, some c87, some c655, some c351, some c657, some c632, some c115, some c66, some c498, some c67, some c49, some c281, some c277, some c43, some c22, some c200, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c79, c25, c653, c639, c644, c654, c87, c655, c351, c657, c632, c115, c66, c498, c67, c49, c281, c277, c43, c22, c200] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c653 := derived653 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c644 := derived644 a h
  have h5 : Entails.eval a c654 := derived654 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c655 := derived655 a h
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c657 := derived657 a h
  have h10 : Entails.eval a c632 := derived632 a h
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c498 := derived498 a h
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c281 := h 280 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c644, some c79, some c25, some c645, some c658, some c226, some c647, some c127, some c87, some c168, some c6, some c158, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c644, c79, c25, c645, c658, c226, c647, c127, c87, c168, c6, c158] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c658 := derived658 a h
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c647 := derived647 a h
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c639, some c361, some c644, some c369, some c226, some c67, some c220, some c310, some c247, some c43, some c23, some c265, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c659, c639, c361, c644, c369, c226, c67, c220, c310, c247, c43, c23, c265] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c644 := derived644 a h
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c226 := h 225 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c644, some c645, some c659, some c113, some c639, some c361, some c660, some c452, some c373, some c371, some c228, some c618, some c30, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c644, c645, c659, c113, c639, c361, c660, c452, c373, c371, c228, c618, c30] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c639 := derived639 a h
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c660 := derived660 a h
  have h7 : Entails.eval a c452 := derived452 a h
  have h8 : Entails.eval a c373 := h 372 (by decide)
  have h9 : Entails.eval a c371 := h 370 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c618 := derived618 a h
  have h12 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨51, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c644, some c361, some c452, some c371, some c228, some c382, some c220, some c224, some c244, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c659, c644, c361, c452, c371, c228, c382, c220, c224, c244] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c452 := derived452 a h
  have h4 : Entails.eval a c371 := h 370 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c382 := derived382 a h
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨47, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c373, some c371, some c356, some c382, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c589, c373, c371, c356, c382] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c382 := derived382 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c644, some c662, some c663, some c351, some c359, some c350, some c650, some c227, some c243, some c219, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c659, c644, c662, c663, c351, c359, c350, c650, c227, c243, c219] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c662 := derived662 a h
  have h3 : Entails.eval a c663 := derived663 a h
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c350 := h 349 (by decide)
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c664, some c226, some c369, some c659, some c644, some c356, some c360, some c352, some c219, some c227, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c589, c664, c226, c369, c659, c644, c356, c360, c352, c219, c227] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c664 := derived664 a h
  have h2 : Entails.eval a c226 := h 225 (by decide)
  have h3 : Entails.eval a c369 := h 368 (by decide)
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c644 := derived644 a h
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c360 := h 359 (by decide)
  have h8 : Entails.eval a c352 := h 351 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨42, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c659, some c644, some c661, some c80, some c664, some c226, some c374, some c665, some c361, some c220, some c245, some c228, some c219, some c355, some c353, some c368, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c589, c659, c644, c661, c80, c664, c226, c374, c665, c361, c220, c245, c228, c219, c355, c353, c368] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c644 := derived644 a h
  have h3 : Entails.eval a c661 := derived661 a h
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c664 := derived664 a h
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c374 := h 373 (by decide)
  have h8 : Entails.eval a c665 := derived665 a h
  have h9 : Entails.eval a c361 := h 360 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c245 := h 244 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c355 := h 354 (by decide)
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c86, some c349, some c355, some c13, some c160, some c166, some c174, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c589, c86, c349, c355, c13, c160, c166, c174] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c349 := h 348 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨46, by decide⟩, true), (⟨17, by decide⟩, true), (⟨42, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c644, some c27, some c127, some c220, some c667, some c360, some c219, some c251, some c33, some c126, some c6, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c659, c644, c27, c127, c220, c667, c360, c219, c251, c33, c126, c6] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c644 := derived644 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c220 := h 219 (by decide)
  have h5 : Entails.eval a c667 := derived667 a h
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c219 := h 218 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c126 := h 125 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨31, by decide⟩, true), (⟨42, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c185, some c26, some c123, some c249, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c6, c185, c26, c123, c249] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨42, by decide⟩, true), (⟨19, by decide⟩, false), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c669, some c126, some c249, some c23, some c123, some c12, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c669, c126, c249, c23, c123, c12] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c669 := derived669 a h
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c249 := h 248 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨42, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c659, some c361, some c668, some c17, some c265, some c644, some c162, some c161, some c182, some c186, some c126, some c249, some c248, some c23, some c123, some c34, some c133, some c16, some c14, some c84, some c82, some c371, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c666, c659, c361, c668, c17, c265, c644, c162, c161, c182, c186, c126, c249, c248, c23, c123, c34, c133, c16, c14, c84, c82, c371] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c668 := derived668 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c644 := derived644 a h
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c186 := h 185 (by decide)
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c248 := h 247 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c133 := h 132 (by decide)
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c84 := h 83 (by decide)
  have h21 : Entails.eval a c82 := h 81 (by decide)
  have h22 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨42, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c659, some c361, some c668, some c17, some c265, some c644, some c671, some c670, some c81, some c91, some c90, some c115, some c26, some c80, some c231, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c666, c659, c361, c668, c17, c265, c644, c671, c670, c81, c91, c90, c115, c26, c80, c231] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c668 := derived668 a h
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c644 := derived644 a h
  have h7 : Entails.eval a c671 := derived671 a h
  have h8 : Entails.eval a c670 := derived670 a h
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c80 := h 79 (by decide)
  have h15 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c68, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c589, c68] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c86, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c589, c86] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨50, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c99, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c589, c99] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c105, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c589, c105] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c106, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c589, c106] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c327, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c589, c327] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨38, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c333, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c589, c333] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨39, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c334, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c589, c334] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived680

end CochromaticTwenty.Certificates.B16_3_1
