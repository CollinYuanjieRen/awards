import MerLeanExperiment.Certificates.B16_8_2.Steps0100_0199

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c581 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c285, some c70, some c154, some c2, some c129, some c171, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c68, c285, c70, c154, c2, c129, c171] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c285 := h 284 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c129, some c309, some c98, some c2, some c149, some c575, some c300, some c69, some c365, some c284, some c80, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c129, c309, c98, c2, c149, c575, c300, c69, c365, c284, c80] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c129 := h 128 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c575 := derived575 a h
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c37, some c342, some c340, some c60, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c300, c37, c342, c340, c60] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  have h3 : Entails.eval a c340 := h 339 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c580, some c556, some c375, some c581, some c583, some c69, some c94, some c98, some c582, some c154, some c285, some c563, some c80, some c81, some c372, some c370, some c354, some c353, some c376, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c580, c556, c375, c581, c583, c69, c94, c98, c582, c154, c285, c563, c80, c81, c372, c370, c354, c353, c376] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c580 := derived580 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c581 := derived581 a h
  have h4 : Entails.eval a c583 := derived583 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c582 := derived582 a h
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c285 := h 284 (by decide)
  have h11 : Entails.eval a c563 := derived563 a h
  have h12 : Entails.eval a c80 := h 79 (by decide)
  have h13 : Entails.eval a c81 := h 80 (by decide)
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c370 := h 369 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c353 := h 352 (by decide)
  have h18 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c580, some c584, some c65, some c87, some c583, some c69, some c365, some c80, some c284, some c37, some c324, some c313, some c55, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c375, c580, c584, c65, c87, c583, c69, c365, c80, c284, c37, c324, c313, c55] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c580 := derived580 a h
  have h2 : Entails.eval a c584 := derived584 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c583 := derived583 a h
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c365 := h 364 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c65, some c87, some c43, some c306, some c274, some c49, some c70, some c453, some c102, some c334, some c56, some c53, some c340, some c313, some c69, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c36, c65, c87, c43, c306, c274, c49, c70, c453, c102, c334, c56, c53, c340, c313, c69] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c306 := h 305 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c453 := derived453 a h
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c334 := h 333 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c340 := h 339 (by decide)
  have h14 : Entails.eval a c313 := h 312 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨41, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c98, some c69, some c324, some c313, some c81, some c261, some c366, some c334, some c154, some c577, some c2, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c94, c98, c69, c324, c313, c81, c261, c366, c334, c154, c577, c2] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c324 := h 323 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c334 := h 333 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c577 := derived577 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c195, some c334, some c349, some c348, some c19, some c88, some c197, some c199, some c23, some c256, some c214, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c265, c195, c334, c349, c348, c19, c88, c197, c199, c23, c256, c214] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c334 := h 333 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c556, some c585, some c586, some c36, some c69, some c94, some c98, some c49, some c304, some c306, some c310, some c48, some c588, some c344, some c63, some c324, some c587, some c81, some c149, some c287, some c2, some c154, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c375, c556, c585, c586, c36, c69, c94, c98, c49, c304, c306, c310, c48, c588, c344, c63, c324, c587, c81, c149, c287, c2, c154] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c588 := derived588 a h
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c324 := h 323 (by decide)
  have h17 : Entails.eval a c587 := derived587 a h
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c149 := h 148 (by decide)
  have h20 : Entails.eval a c287 := h 286 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c556, some c585, some c586, some c36, some c589, some c340, some c37, some c302, some c48, some c99, some c49, some c63, some c306, some c310, some c344, some c265, some c195, some c349, some c19, some c250, some c197, some c199, some c218, some c257, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c375, c556, c585, c586, c36, c589, c340, c37, c302, c48, c99, c49, c63, c306, c310, c344, c265, c195, c349, c19, c250, c197, c199, c218, c257] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c589 := derived589 a h
  have h6 : Entails.eval a c340 := h 339 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c344 := h 343 (by decide)
  have h16 : Entails.eval a c265 := h 264 (by decide)
  have h17 : Entails.eval a c195 := h 194 (by decide)
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c199 := h 198 (by decide)
  have h23 : Entails.eval a c218 := h 217 (by decide)
  have h24 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨1, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c195, some c349, some c348, some c19, some c197, some c199, some c257, some c256, some c214, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c265, c195, c349, c348, c19, c197, c199, c257, c256, c214] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c195 := h 194 (by decide)
  have h2 : Entails.eval a c349 := h 348 (by decide)
  have h3 : Entails.eval a c348 := h 347 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c257 := h 256 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c556, some c585, some c586, some c36, some c304, some c306, some c310, some c48, some c99, some c591, some c344, some c342, some c63, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c375, c556, c585, c586, c36, c304, c306, c310, c48, c99, c591, c344, c342, c63] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c591 := derived591 a h
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c342 := h 341 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c590, some c68, some c375, some c556, some c585, some c586, some c36, some c592, some c49, some c98, some c99, some c70, some c325, some c64, some c62, some c342, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c590, c68, c375, c556, c585, c586, c36, c592, c49, c98, c99, c70, c325, c64, c62, c342] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c590 := derived590 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c585 := derived585 a h
  have h5 : Entails.eval a c586 := derived586 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c592 := derived592 a h
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c375, some c585, some c36, some c586, some c590, some c68, some c593, some c69, some c94, some c324, some c98, some c63, some c49, some c344, some c304, some c306, some c310, some c39, some c591, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c556, c375, c585, c36, c586, c590, c68, c593, c69, c94, c324, c98, c63, c49, c344, c304, c306, c310, c39, c591] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c586 := derived586 a h
  have h5 : Entails.eval a c590 := derived590 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c593 := derived593 a h
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c324 := h 323 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c304 := h 303 (by decide)
  have h16 : Entails.eval a c306 := h 305 (by decide)
  have h17 : Entails.eval a c310 := h 309 (by decide)
  have h18 : Entails.eval a c39 := h 38 (by decide)
  have h19 : Entails.eval a c591 := derived591 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨36, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c99, some c591, some c344, some c63, some c351, some c345, some c342, some c59, some c261, some c189, some c94, some c349, some c18, some c19, some c214, some c204, some c25, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c556, c99, c591, c344, c63, c351, c345, c342, c59, c261, c189, c94, c349, c18, c19, c214, c204, c25] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c591 := derived591 a h
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c189 := h 188 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c214 := h 213 (by decide)
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c101, some c100, some c94, some c90, some c380, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c101, c100, c94, c90, c380] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c101 := h 100 (by decide)
  have h1 : Entails.eval a c100 := h 99 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c45, some c302, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c44, c45, c302] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c77, some c76, some c365, some c372, some c354, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c77, c76, c365, c372, c354] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c77 := h 76 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c594, some c596, some c375, some c380, some c597, some c310, some c598, some c279, some c70, some c98, some c40, some c51, some c344, some c302, some c39, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c556, c594, c596, c375, c380, c597, c310, c598, c279, c70, c98, c40, c51, c344, c302, c39] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c597 := derived597 a h
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c598 := derived598 a h
  have h8 : Entails.eval a c279 := h 278 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c302 := h 301 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c336, some c57, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c344, c336, c57] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c594, some c596, some c599, some c94, some c88, some c98, some c600, some c40, some c304, some c310, some c45, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c556, c594, c596, c599, c94, c88, c98, c600, c40, c304, c310, c45] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c599 := derived599 a h
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c600 := derived600 a h
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c310 := h 309 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨36, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c601, some c594, some c304, some c306, some c310, some c595, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c601, c594, c304, c306, c310, c595] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c601 := derived601 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c304 := h 303 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c310 := h 309 (by decide)
  have h5 : Entails.eval a c595 := derived595 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨26, by decide⟩, false), (⟨50, by decide⟩, false), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨32, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c99, some c556, some c375, some c252, some c19, some c404, some c293, some c282, some c358, some c354, some c313, some c274, some c189, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c99, c556, c375, c252, c19, c404, c293, c282, c358, c354, c313, c274, c189] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c99 := h 98 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c404 := derived404 a h
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c189 := h 188 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨36, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c601, some c99, some c602, some c40, some c344, some c51, some c556, some c594, some c596, some c69, some c88, some c336, some c34, some c56, some c351, some c603, some c195, some c213, some c312, some c244, some c47, some c191, some c205, some c25, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c601, c99, c602, c40, c344, c51, c556, c594, c596, c69, c88, c336, c34, c56, c351, c603, c195, c213, c312, c244, c47, c191, c205, c25] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c601 := derived601 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c602 := derived602 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c556 := derived556 a h
  have h7 : Entails.eval a c594 := derived594 a h
  have h8 : Entails.eval a c596 := derived596 a h
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c336 := h 335 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c351 := h 350 (by decide)
  have h15 : Entails.eval a c603 := derived603 a h
  have h16 : Entails.eval a c195 := h 194 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  have h18 : Entails.eval a c312 := h 311 (by decide)
  have h19 : Entails.eval a c244 := h 243 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c205 := h 204 (by decide)
  have h23 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨51, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c279, some c277, some c358, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c279, c277, c358] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c279 := h 278 (by decide)
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, false), (⟨51, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c252, some c601, some c99, some c404, some c51, some c40, some c556, some c594, some c596, some c605, some c66, some c76, some c336, some c603, some c56, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c252, c601, c99, c404, c51, c40, c556, c594, c596, c605, c66, c76, c336, c603, c56] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c601 := derived601 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c404 := derived404 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c556 := derived556 a h
  have h7 : Entails.eval a c594 := derived594 a h
  have h8 : Entails.eval a c596 := derived596 a h
  have h9 : Entails.eval a c605 := derived605 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c603 := derived603 a h
  have h14 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c601, some c99, some c556, some c594, some c596, some c375, some c602, some c40, some c51, some c344, some c604, some c302, some c380, some c195, some c252, some c250, some c606, some c34, some c349, some c336, some c409, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c601, c99, c556, c594, c596, c375, c602, c40, c51, c344, c604, c302, c380, c195, c252, c250, c606, c34, c349, c336, c409] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c601 := derived601 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c602 := derived602 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c604 := derived604 a h
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c252 := h 251 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  have h16 : Entails.eval a c606 := derived606 a h
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c336 := h 335 (by decide)
  have h20 : Entails.eval a c409 := derived409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c607, some c192, some c601, some c99, some c556, some c594, some c596, some c40, some c51, some c344, some c268, some c302, some c305, some c69, some c94, some c88, some c263, some c29, some c336, some c346, some c34, some c56, some c220, some c603, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c607, c192, c601, c99, c556, c594, c596, c40, c51, c344, c268, c302, c305, c69, c94, c88, c263, c29, c336, c346, c34, c56, c220, c603] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c607 := derived607 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c601 := derived601 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c594 := derived594 a h
  have h6 : Entails.eval a c596 := derived596 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  have h18 : Entails.eval a c336 := h 335 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c56 := h 55 (by decide)
  have h22 : Entails.eval a c220 := h 219 (by decide)
  have h23 : Entails.eval a c603 := derived603 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c601, some c99, some c607, some c608, some c304, some c306, some c268, some c263, some c344, some c345, some c63, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c601, c99, c607, c608, c304, c306, c268, c263, c344, c345, c63] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c601 := derived601 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c607 := derived607 a h
  have h3 : Entails.eval a c608 := derived608 a h
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c344, some c63, some c352, some c345, some c262, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c344, c63, c352, c345, c262] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c344 := h 343 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c352 := h 351 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c594, some c596, some c609, some c309, some c34, some c413, some c601, some c99, some c304, some c306, some c610, some c195, some c252, some c19, some c198, some c197, some c27, some c247, some c256, some c67, some c35, some c225, some c66, some c348, some c336, some c217, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c556, c594, c596, c609, c309, c34, c413, c601, c99, c304, c306, c610, c195, c252, c19, c198, c197, c27, c247, c256, c67, c35, c225, c66, c348, c336, c217] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c609 := derived609 a h
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c413 := derived413 a h
  have h7 : Entails.eval a c601 := derived601 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c306 := h 305 (by decide)
  have h11 : Entails.eval a c610 := derived610 a h
  have h12 : Entails.eval a c195 := h 194 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c247 := h 246 (by decide)
  have h19 : Entails.eval a c256 := h 255 (by decide)
  have h20 : Entails.eval a c67 := h 66 (by decide)
  have h21 : Entails.eval a c35 := h 34 (by decide)
  have h22 : Entails.eval a c225 := h 224 (by decide)
  have h23 : Entails.eval a c66 := h 65 (by decide)
  have h24 : Entails.eval a c348 := h 347 (by decide)
  have h25 : Entails.eval a c336 := h 335 (by decide)
  have h26 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c594, some c596, some c601, some c99, some c609, some c413, some c309, some c44, some c34, some c611, some c40, some c344, some c336, some c88, some c302, some c195, some c252, some c404, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c556, c594, c596, c601, c99, c609, c413, c309, c44, c34, c611, c40, c344, c336, c88, c302, c195, c252, c404] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c601 := derived601 a h
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c609 := derived609 a h
  have h6 : Entails.eval a c413 := derived413 a h
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c611 := derived611 a h
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c195 := h 194 (by decide)
  have h17 : Entails.eval a c252 := h 251 (by decide)
  have h18 : Entails.eval a c404 := derived404 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c612, some c65, some c556, some c594, some c596, some c85, some c336, some c34, some c56, some c53, some c313, some c316, some c69, some c76, some c83, some c380, some c279, some c70, some c154, some c358, some c15, some c13, some c368, some c165, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c375, c612, c65, c556, c594, c596, c85, c336, c34, c56, c53, c313, c316, c69, c76, c83, c380, c279, c70, c154, c358, c15, c13, c368, c165] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c612 := derived612 a h
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c594 := derived594 a h
  have h5 : Entails.eval a c596 := derived596 a h
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c336 := h 335 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c83 := h 82 (by decide)
  have h16 : Entails.eval a c380 := h 379 (by decide)
  have h17 : Entails.eval a c279 := h 278 (by decide)
  have h18 : Entails.eval a c70 := h 69 (by decide)
  have h19 : Entails.eval a c154 := h 153 (by decide)
  have h20 : Entails.eval a c358 := h 357 (by decide)
  have h21 : Entails.eval a c15 := h 14 (by decide)
  have h22 : Entails.eval a c13 := h 12 (by decide)
  have h23 : Entails.eval a c368 := h 367 (by decide)
  have h24 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨34, by decide⟩, false), (⟨39, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c40, some c85, some c309, some c269, some c349, some c348, some c220, some c267, some c31, some c293, some c605, some c70, some c62, some c76, some c550, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c196, c40, c85, c309, c269, c349, c348, c220, c267, c31, c293, c605, c70, c62, c76, c550] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c220 := h 219 (by decide)
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c293 := h 292 (by decide)
  have h11 : Entails.eval a c605 := derived605 a h
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c550 := derived550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c195, some c213, some c614, some c44, some c41, some c305, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c195, c213, c614, c44, c41, c305] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c195 := h 194 (by decide)
  have h1 : Entails.eval a c213 := h 212 (by decide)
  have h2 : Entails.eval a c614 := derived614 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c41, some c201, some c305, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c44, c41, c201, c305] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨31, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c305, some c312, some c33, some c267, some c345, some c348, some c56, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c305, c312, c33, c267, c345, c348, c56] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c305 := h 304 (by decide)
  have h1 : Entails.eval a c312 := h 311 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, false), (⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c596, some c85, some c342, some c345, some c69, some c94, some c53, some c324, some c550, some c334, some c152, some c154, some c13, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c596, c85, c342, c345, c69, c94, c53, c324, c550, c334, c152, c154, c13] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c596 := derived596 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c550 := derived550 a h
  have h9 : Entails.eval a c334 := h 333 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c613, some c612, some c375, some c556, some c594, some c596, some c85, some c196, some c252, some c244, some c615, some c616, some c309, some c269, some c618, some c37, some c56, some c617, some c349, some c348, some c204, some c62, some c407, some c29, some c259, some c214, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c613, c612, c375, c556, c594, c596, c85, c196, c252, c244, c615, c616, c309, c269, c618, c37, c56, c617, c349, c348, c204, c62, c407, c29, c259, c214] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c612 := derived612 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c594 := derived594 a h
  have h5 : Entails.eval a c596 := derived596 a h
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c615 := derived615 a h
  have h11 : Entails.eval a c616 := derived616 a h
  have h12 : Entails.eval a c309 := h 308 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c618 := derived618 a h
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c56 := h 55 (by decide)
  have h17 : Entails.eval a c617 := derived617 a h
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c348 := h 347 (by decide)
  have h20 : Entails.eval a c204 := h 203 (by decide)
  have h21 : Entails.eval a c62 := h 61 (by decide)
  have h22 : Entails.eval a c407 := derived407 a h
  have h23 : Entails.eval a c29 := h 28 (by decide)
  have h24 : Entails.eval a c259 := h 258 (by decide)
  have h25 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c594, some c596, some c612, some c619, some c306, some c310, some c41, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c556, c594, c596, c612, c619, c306, c310, c41] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c612 := derived612 a h
  have h4 : Entails.eval a c619 := derived619 a h
  have h5 : Entails.eval a c306 := h 305 (by decide)
  have h6 : Entails.eval a c310 := h 309 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c306, some c310, some c41, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c306, c310, c41] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c306 := h 305 (by decide)
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨51, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c336, some c333, some c196, some c267, some c252, some c244, some c299, some c201, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c34, c336, c333, c196, c267, c252, c244, c299, c201] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c336 := h 335 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c252 := h 251 (by decide)
  have h6 : Entails.eval a c244 := h 243 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c621, some c375, some c85, some c65, some c620, some c556, some c103, some c86, some c376, some c622, some c293, some c42, some c274, some c70, some c154, some c13, some c118, some c171, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c621, c375, c85, c65, c620, c556, c103, c86, c376, c622, c293, c42, c274, c70, c154, c13, c118, c171] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c621 := derived621 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c620 := derived620 a h
  have h5 : Entails.eval a c556 := derived556 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c622 := derived622 a h
  have h10 : Entails.eval a c293 := h 292 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c274 := h 273 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  have h17 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c43, some c48, some c334, some c305, some c57, some c53, some c271, some c345, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c36, c43, c48, c334, c305, c57, c53, c271, c345] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c334 := h 333 (by decide)
  have h4 : Entails.eval a c305 := h 304 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c375, some c85, some c621, some c623, some c87, some c376, some c86, some c104, some c600, some c40, some c196, some c252, some c624, some c309, some c34, some c41, some c427, some c334, some c305, some c60, some c55, some c271, some c345, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c620, c375, c85, c621, c623, c87, c376, c86, c104, c600, c40, c196, c252, c624, c309, c34, c41, c427, c334, c305, c60, c55, c271, c345] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c621 := derived621 a h
  have h4 : Entails.eval a c623 := derived623 a h
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c600 := derived600 a h
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c624 := derived624 a h
  have h14 : Entails.eval a c309 := h 308 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c427 := derived427 a h
  have h18 : Entails.eval a c334 := h 333 (by decide)
  have h19 : Entails.eval a c305 := h 304 (by decide)
  have h20 : Entails.eval a c60 := h 59 (by decide)
  have h21 : Entails.eval a c55 := h 54 (by decide)
  have h22 : Entails.eval a c271 := h 270 (by decide)
  have h23 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c620, some c103, some c87, some c104, some c625, some c65, some c556, some c274, some c70, some c154, some c102, some c49, some c40, some c569, some c576, some c571, some c129, some c344, some c265, some c190, some c113, some c60, some c305, some c21, some c23, some c147, some c264, some c214, some c351, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c375, c620, c103, c87, c104, c625, c65, c556, c274, c70, c154, c102, c49, c40, c569, c576, c571, c129, c344, c265, c190, c113, c60, c305, c21, c23, c147, c264, c214, c351] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c625 := derived625 a h
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c569 := derived569 a h
  have h15 : Entails.eval a c576 := derived576 a h
  have h16 : Entails.eval a c571 := derived571 a h
  have h17 : Entails.eval a c129 := h 128 (by decide)
  have h18 : Entails.eval a c344 := h 343 (by decide)
  have h19 : Entails.eval a c265 := h 264 (by decide)
  have h20 : Entails.eval a c190 := h 189 (by decide)
  have h21 : Entails.eval a c113 := h 112 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  have h23 : Entails.eval a c305 := h 304 (by decide)
  have h24 : Entails.eval a c21 := h 20 (by decide)
  have h25 : Entails.eval a c23 := h 22 (by decide)
  have h26 : Entails.eval a c147 := h 146 (by decide)
  have h27 : Entails.eval a c264 := h 263 (by decide)
  have h28 : Entails.eval a c214 := h 213 (by decide)
  have h29 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨3, by decide⟩, false), (⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c103, some c626, some c43, some c33, some c375, some c87, some c376, some c104, some c625, some c65, some c556, some c344, some c336, some c316, some c346, some c190, some c64, some c244, some c21, some c102, some c203, some c563, some c81, some c358, some c281, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c620, c103, c626, c43, c33, c375, c87, c376, c104, c625, c65, c556, c344, c336, c316, c346, c190, c64, c244, c21, c102, c203, c563, c81, c358, c281] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c626 := derived626 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c625 := derived625 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c556 := derived556 a h
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c336 := h 335 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c346 := h 345 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c244 := h 243 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c102 := h 101 (by decide)
  have h21 : Entails.eval a c203 := h 202 (by decide)
  have h22 : Entails.eval a c563 := derived563 a h
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c358 := h 357 (by decide)
  have h25 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c625, some c375, some c65, some c620, some c556, some c103, some c104, some c626, some c33, some c43, some c627, some c40, some c102, some c70, some c285, some c314, some c80, some c64, some c315, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c625, c375, c65, c620, c556, c103, c104, c626, c33, c43, c627, c40, c102, c70, c285, c314, c80, c64, c315] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c625 := derived625 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c620 := derived620 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c626 := derived626 a h
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c627 := derived627 a h
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c625, some c375, some c65, some c556, some c628, some c86, some c376, some c87, some c101, some c70, some c274, some c557, some c42, some c58, some c299, some c339, some c333, some c265, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c625, c375, c65, c556, c628, c86, c376, c87, c101, c70, c274, c557, c42, c58, c299, c339, c333, c265] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c625 := derived625 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c628 := derived628 a h
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c557 := derived557 a h
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c299 := h 298 (by decide)
  have h15 : Entails.eval a c339 := h 338 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c86, some c65, some c620, some c556, some c70, some c274, some c557, some c42, some c58, some c299, some c339, some c265, some c39, some c195, some c348, some c252, some c30, some c268, some c207, some c311, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c375, c86, c65, c620, c556, c70, c274, c557, c42, c58, c299, c339, c265, c39, c195, c348, c252, c30, c268, c207, c311] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c620 := derived620 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c557 := derived557 a h
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c195 := h 194 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c30 := h 29 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c207 := h 206 (by decide)
  have h20 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c625, some c375, some c86, some c630, some c101, some c102, some c87, some c49, some c47, some c297, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c625, c375, c86, c630, c101, c102, c87, c49, c47, c297] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c625 := derived625 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c101 := h 100 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c620, some c631, some c103, some c87, some c104, some c629, some c625, some c65, some c556, some c102, some c49, some c40, some c563, some c344, some c154, some c60, some c7, some c169, some c150, some c118, some c33, some c316, some c81, some c318, some c368, some c190, some c358, some c21, some c297, some c337, some c191, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c375, c620, c631, c103, c87, c104, c629, c625, c65, c556, c102, c49, c40, c563, c344, c154, c60, c7, c169, c150, c118, c33, c316, c81, c318, c368, c190, c358, c21, c297, c337, c191] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c629 := derived629 a h
  have h7 : Entails.eval a c625 := derived625 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c563 := derived563 a h
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c60 := h 59 (by decide)
  have h17 : Entails.eval a c7 := h 6 (by decide)
  have h18 : Entails.eval a c169 := h 168 (by decide)
  have h19 : Entails.eval a c150 := h 149 (by decide)
  have h20 : Entails.eval a c118 := h 117 (by decide)
  have h21 : Entails.eval a c33 := h 32 (by decide)
  have h22 : Entails.eval a c316 := h 315 (by decide)
  have h23 : Entails.eval a c81 := h 80 (by decide)
  have h24 : Entails.eval a c318 := h 317 (by decide)
  have h25 : Entails.eval a c368 := h 367 (by decide)
  have h26 : Entails.eval a c190 := h 189 (by decide)
  have h27 : Entails.eval a c358 := h 357 (by decide)
  have h28 : Entails.eval a c21 := h 20 (by decide)
  have h29 : Entails.eval a c297 := h 296 (by decide)
  have h30 : Entails.eval a c337 := h 336 (by decide)
  have h31 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c65, some c620, some c556, some c631, some c103, some c104, some c632, some c70, some c274, some c557, some c33, some c43, some c64, some c285, some c315, some c80, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c375, c65, c620, c556, c631, c103, c104, c632, c70, c274, c557, c33, c43, c64, c285, c315, c80] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c632 := derived632 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c274 := h 273 (by decide)
  have h10 : Entails.eval a c557 := derived557 a h
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨28, by decide⟩, true), (⟨32, by decide⟩, true), (⟨2, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c43, some c49, some c274, some c102, some c70, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c43, c49, c274, c102, c70] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c625, some c375, some c65, some c620, some c556, some c633, some c309, some c634, some c103, some c101, some c86, some c70, some c279, some c274, some c557, some c33, some c42, some c58, some c293, some c299, some c339, some c150, some c268, some c195, some c6, some c121, some c337, some c252, some c247, some c171, some c196, some c111, some c136, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c625, c375, c65, c620, c556, c633, c309, c634, c103, c101, c86, c70, c279, c274, c557, c33, c42, c58, c293, c299, c339, c150, c268, c195, c6, c121, c337, c252, c247, c171, c196, c111, c136] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c625 := derived625 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c620 := derived620 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c633 := derived633 a h
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c634 := derived634 a h
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c274 := h 273 (by decide)
  have h14 : Entails.eval a c557 := derived557 a h
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c42 := h 41 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c299 := h 298 (by decide)
  have h20 : Entails.eval a c339 := h 338 (by decide)
  have h21 : Entails.eval a c150 := h 149 (by decide)
  have h22 : Entails.eval a c268 := h 267 (by decide)
  have h23 : Entails.eval a c195 := h 194 (by decide)
  have h24 : Entails.eval a c6 := h 5 (by decide)
  have h25 : Entails.eval a c121 := h 120 (by decide)
  have h26 : Entails.eval a c337 := h 336 (by decide)
  have h27 : Entails.eval a c252 := h 251 (by decide)
  have h28 : Entails.eval a c247 := h 246 (by decide)
  have h29 : Entails.eval a c171 := h 170 (by decide)
  have h30 : Entails.eval a c196 := h 195 (by decide)
  have h31 : Entails.eval a c111 := h 110 (by decide)
  have h32 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c86, some c380, some c65, some c101, some c70, some c557, some c58, some c339, some c265, some c333, some c348, some c268, some c565, some c285, some c152, some c12, some c6, some c172, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c86, c380, c65, c101, c70, c557, c58, c339, c265, c333, c348, c268, c565, c285, c152, c12, c6, c172] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c101 := h 100 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c557 := derived557 a h
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c565 := derived565 a h
  have h13 : Entails.eval a c285 := h 284 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c12 := h 11 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨55, by decide⟩, false), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c87, some c43, some c565, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c636, c87, c43, c565] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c565 := derived565 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨36, by decide⟩, false), (⟨10, by decide⟩, true), (⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨37, by decide⟩, true), (⟨28, by decide⟩, false), (⟨52, by decide⟩, false), (⟨26, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c376, some c362, some c150, some c284, some c318, some c264, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c380, c376, c362, c150, c284, c318, c264] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c362 := h 361 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c556, some c375, some c65, some c625, some c635, some c304, some c306, some c310, some c33, some c637, some c103, some c104, some c87, some c43, some c39, some c344, some c345, some c315, some c80, some c285, some c70, some c154, some c102, some c7, some c61, some c638, some c358, some c281, some c321, some c368, some c191, some c150, some c26, some c21, some c334, some c212, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c620, c556, c375, c65, c625, c635, c304, c306, c310, c33, c637, c103, c104, c87, c43, c39, c344, c345, c315, c80, c285, c70, c154, c102, c7, c61, c638, c358, c281, c321, c368, c191, c150, c26, c21, c334, c212] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c625 := derived625 a h
  have h5 : Entails.eval a c635 := derived635 a h
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c637 := derived637 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c345 := h 344 (by decide)
  have h18 : Entails.eval a c315 := h 314 (by decide)
  have h19 : Entails.eval a c80 := h 79 (by decide)
  have h20 : Entails.eval a c285 := h 284 (by decide)
  have h21 : Entails.eval a c70 := h 69 (by decide)
  have h22 : Entails.eval a c154 := h 153 (by decide)
  have h23 : Entails.eval a c102 := h 101 (by decide)
  have h24 : Entails.eval a c7 := h 6 (by decide)
  have h25 : Entails.eval a c61 := h 60 (by decide)
  have h26 : Entails.eval a c638 := derived638 a h
  have h27 : Entails.eval a c358 := h 357 (by decide)
  have h28 : Entails.eval a c281 := h 280 (by decide)
  have h29 : Entails.eval a c321 := h 320 (by decide)
  have h30 : Entails.eval a c368 := h 367 (by decide)
  have h31 : Entails.eval a c191 := h 190 (by decide)
  have h32 : Entails.eval a c150 := h 149 (by decide)
  have h33 : Entails.eval a c26 := h 25 (by decide)
  have h34 : Entails.eval a c21 := h 20 (by decide)
  have h35 : Entails.eval a c334 := h 333 (by decide)
  have h36 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨32, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c310, some c2, some c7, some c131, some c129, some c169, some c576, some c571, some c113, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c98, c310, c2, c7, c131, c129, c169, c576, c571, c113] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c310 := h 309 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c169 := h 168 (by decide)
  have h7 : Entails.eval a c576 := derived576 a h
  have h8 : Entails.eval a c571 := derived571 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c556, some c639, some c620, some c97, some c304, some c48, some c581, some c310, some c45, some c98, some c640, some c154, some c287, some c285, some c81, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c375, c556, c639, c620, c97, c304, c48, c581, c310, c45, c98, c640, c154, c287, c285, c81] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c620 := derived620 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c581 := derived581 a h
  have h8 : Entails.eval a c310 := h 309 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c98 := h 97 (by decide)
  have h11 : Entails.eval a c640 := derived640 a h
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c287 := h 286 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c641, some c70, some c287, some c620, some c639, some c97, some c304, some c48, some c285, some c81, some c375, some c581, some c39, some c344, some c310, some c376, some c90, some c499, some c178, some c300, some c342, some c392, some c193, some c264, some c427, some c248, some c334, some c217, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c556, c641, c70, c287, c620, c639, c97, c304, c48, c285, c81, c375, c581, c39, c344, c310, c376, c90, c499, c178, c300, c342, c392, c193, c264, c427, c248, c334, c217] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c641 := derived641 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c620 := derived620 a h
  have h5 : Entails.eval a c639 := derived639 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c375 := h 374 (by decide)
  have h12 : Entails.eval a c581 := derived581 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c310 := h 309 (by decide)
  have h16 : Entails.eval a c376 := h 375 (by decide)
  have h17 : Entails.eval a c90 := h 89 (by decide)
  have h18 : Entails.eval a c499 := derived499 a h
  have h19 : Entails.eval a c178 := h 177 (by decide)
  have h20 : Entails.eval a c300 := h 299 (by decide)
  have h21 : Entails.eval a c342 := h 341 (by decide)
  have h22 : Entails.eval a c392 := derived392 a h
  have h23 : Entails.eval a c193 := h 192 (by decide)
  have h24 : Entails.eval a c264 := h 263 (by decide)
  have h25 : Entails.eval a c427 := derived427 a h
  have h26 : Entails.eval a c248 := h 247 (by decide)
  have h27 : Entails.eval a c334 := h 333 (by decide)
  have h28 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, false), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨28, by decide⟩, false), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c90, some c174, some c499, some c5, some c172, some c169, some c300, some c342, some c4, some c193, some c264, some c165, some c26, some c348, some c125, some c191, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c90, c174, c499, c5, c172, c169, c300, c342, c4, c193, c264, c165, c26, c348, c125, c191] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c499 := derived499 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c348 := h 347 (by decide)
  have h14 : Entails.eval a c125 := h 124 (by decide)
  have h15 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨14, by decide⟩, true), (⟨47, by decide⟩, false), (⟨52, by decide⟩, false), (⟨28, by decide⟩, false), (⟨39, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c380, some c297, some c339, some c178, some c262, some c1, some c315, some c149, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c380, c297, c339, c178, c262, c1, c315, c149] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c380 := h 379 (by decide)
  have h1 : Entails.eval a c297 := h 296 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨37, by decide⟩, true), (⟨53, by decide⟩, false), (⟨36, by decide⟩, true), (⟨52, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c217, some c248, some c219, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c217, c248, c219] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c217 := h 216 (by decide)
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c641, some c70, some c287, some c620, some c639, some c97, some c304, some c48, some c285, some c81, some c80, some c375, some c581, some c39, some c344, some c310, some c45, some c306, some c642, some c644, some c90, some c643, some c499, some c178, some c342, some c392, some c645, some c427, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c556, c641, c70, c287, c620, c639, c97, c304, c48, c285, c81, c80, c375, c581, c39, c344, c310, c45, c306, c642, c644, c90, c643, c499, c178, c342, c392, c645, c427] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c641 := derived641 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c620 := derived620 a h
  have h5 : Entails.eval a c639 := derived639 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c375 := h 374 (by decide)
  have h13 : Entails.eval a c581 := derived581 a h
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c344 := h 343 (by decide)
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c306 := h 305 (by decide)
  have h19 : Entails.eval a c642 := derived642 a h
  have h20 : Entails.eval a c644 := derived644 a h
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c643 := derived643 a h
  have h23 : Entails.eval a c499 := derived499 a h
  have h24 : Entails.eval a c178 := h 177 (by decide)
  have h25 : Entails.eval a c342 := h 341 (by decide)
  have h26 : Entails.eval a c392 := derived392 a h
  have h27 : Entails.eval a c645 := derived645 a h
  have h28 : Entails.eval a c427 := derived427 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c304, some c620, some c639, some c97, some c556, some c48, some c641, some c70, some c287, some c285, some c646, some c131, some c129, some c165, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c304, c620, c639, c97, c556, c48, c641, c70, c287, c285, c646, c131, c129, c165] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c304 := h 303 (by decide)
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c641 := derived641 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c287 := h 286 (by decide)
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c646 := derived646 a h
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c129 := h 128 (by decide)
  have h13 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, true), (⟨46, by decide⟩, false), (⟨51, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c297, some c285, some c152, some c12, some c129, some c178, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c297, c285, c152, c12, c129, c178] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c297 := h 296 (by decide)
  have h1 : Entails.eval a c285 := h 284 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨28, by decide⟩, true), (⟨38, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c261, some c349, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c263, c261, c349] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c639, some c97, some c556, some c375, some c304, some c306, some c310, some c45, some c39, some c647, some c103, some c101, some c90, some c70, some c380, some c339, some c35, some c58, some c648, some c649, some c314, some c149, some c1, some c134, some c178, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c620, c639, c97, c556, c375, c304, c306, c310, c45, c39, c647, c103, c101, c90, c70, c380, c339, c35, c58, c648, c649, c314, c149, c1, c134, c178] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c375 := h 374 (by decide)
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c647 := derived647 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c339 := h 338 (by decide)
  have h17 : Entails.eval a c35 := h 34 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c648 := derived648 a h
  have h20 : Entails.eval a c649 := derived649 a h
  have h21 : Entails.eval a c314 := h 313 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c1 := h 0 (by decide)
  have h24 : Entails.eval a c134 := h 133 (by decide)
  have h25 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨6, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c620, some c103, some c90, some c650, some c639, some c97, some c35, some c299, some c39, some c344, some c40, some c196, some c269, some c252, some c478, some c204, some c427, some c28, some c293, some c466, some c66, some c22, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c556, c620, c103, c90, c650, c639, c97, c35, c299, c39, c344, c40, c196, c269, c252, c478, c204, c427, c28, c293, c466, c66, c22] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c103 := h 102 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c639 := derived639 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c40 := h 39 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c252 := h 251 (by decide)
  have h15 : Entails.eval a c478 := derived478 a h
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c427 := derived427 a h
  have h18 : Entails.eval a c28 := h 27 (by decide)
  have h19 : Entails.eval a c293 := h 292 (by decide)
  have h20 : Entails.eval a c466 := derived466 a h
  have h21 : Entails.eval a c66 := h 65 (by decide)
  have h22 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨46, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c325, some c337, some c152, some c12, some c145, some c178, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c325, c337, c152, c12, c145, c178] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c325 := h 324 (by decide)
  have h1 : Entails.eval a c337 := h 336 (by decide)
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c103, some c650, some c639, some c97, some c556, some c70, some c90, some c380, some c651, some c339, some c39, some c64, some c299, some c47, some c652, some c269, some c192, some c346, some c350, some c28, some c263, some c305, some c207, some c252, some c213, some c57, some c24, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c620, c103, c650, c639, c97, c556, c70, c90, c380, c651, c339, c39, c64, c299, c47, c652, c269, c192, c346, c350, c28, c263, c305, c207, c252, c213, c57, c24] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c650 := derived650 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c556 := derived556 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c651 := derived651 a h
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c652 := derived652 a h
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c192 := h 191 (by decide)
  have h18 : Entails.eval a c346 := h 345 (by decide)
  have h19 : Entails.eval a c350 := h 349 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c263 := h 262 (by decide)
  have h22 : Entails.eval a c305 := h 304 (by decide)
  have h23 : Entails.eval a c207 := h 206 (by decide)
  have h24 : Entails.eval a c252 := h 251 (by decide)
  have h25 : Entails.eval a c213 := h 212 (by decide)
  have h26 : Entails.eval a c57 := h 56 (by decide)
  have h27 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c650, some c639, some c98, some c40, some c620, some c97, some c101, some c344, some c57, some c350, some c103, some c47, some c39, some c312, some c28, some c29, some c207, some c220, some c252, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c650, c639, c98, c40, c620, c97, c101, c344, c57, c350, c103, c47, c39, c312, c28, c29, c207, c220, c252] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c650 := derived650 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c620 := derived620 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c350 := h 349 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c207 := h 206 (by decide)
  have h17 : Entails.eval a c220 := h 219 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true), (⟨36, by decide⟩, false), (⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c164, some c109, some c138, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c164, c109, c138] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c164 := h 163 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c103, some c650, some c639, some c97, some c375, some c653, some c101, some c98, some c40, some c47, some c344, some c600, some c39, some c57, some c66, some c299, some c350, some c67, some c283, some c368, some c654, some c192, some c205, some c252, some c220, some c254, some c258, some c199, some c655, some c119, some c127, some c170, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c620, c103, c650, c639, c97, c375, c653, c101, c98, c40, c47, c344, c600, c39, c57, c66, c299, c350, c67, c283, c368, c654, c192, c205, c252, c220, c254, c258, c199, c655, c119, c127, c170] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c650 := derived650 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c653 := derived653 a h
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c600 := derived600 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c350 := h 349 (by decide)
  have h18 : Entails.eval a c67 := h 66 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c368 := h 367 (by decide)
  have h21 : Entails.eval a c654 := derived654 a h
  have h22 : Entails.eval a c192 := h 191 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c252 := h 251 (by decide)
  have h25 : Entails.eval a c220 := h 219 (by decide)
  have h26 : Entails.eval a c254 := h 253 (by decide)
  have h27 : Entails.eval a c258 := h 257 (by decide)
  have h28 : Entails.eval a c199 := h 198 (by decide)
  have h29 : Entails.eval a c655 := derived655 a h
  have h30 : Entails.eval a c119 := h 118 (by decide)
  have h31 : Entails.eval a c127 := h 126 (by decide)
  have h32 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨36, by decide⟩, false), (⟨31, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨3, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c254, some c258, some c190, some c197, some c348, some c35, some c299, some c67, some c281, some c283, some c655, some c119, some c127, some c170, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c254, c258, c190, c197, c348, c35, c299, c67, c281, c283, c655, c119, c127, c170] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c254 := h 253 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c190 := h 189 (by decide)
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c299 := h 298 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c281 := h 280 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c655 := derived655 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c639, some c97, some c39, some c656, some c309, some c103, some c650, some c556, some c375, some c252, some c657, some c220, some c349, some c190, some c57, some c101, some c24, some c70, some c90, some c47, some c648, some c380, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c620, c639, c97, c39, c656, c309, c103, c650, c556, c375, c252, c657, c220, c349, c190, c57, c101, c24, c70, c90, c47, c648, c380] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c252 := h 251 (by decide)
  have h11 : Entails.eval a c657 := derived657 a h
  have h12 : Entails.eval a c220 := h 219 (by decide)
  have h13 : Entails.eval a c349 := h 348 (by decide)
  have h14 : Entails.eval a c190 := h 189 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c24 := h 23 (by decide)
  have h18 : Entails.eval a c70 := h 69 (by decide)
  have h19 : Entails.eval a c90 := h 89 (by decide)
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c648 := derived648 a h
  have h22 : Entails.eval a c380 := h 379 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, true), (⟨26, by decide⟩, true), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c349, some c346, some c57, some c261, some c101, some c305, some c90, some c264, some c299, some c351, some c35, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c39, c349, c346, c57, c261, c101, c305, c90, c264, c299, c351, c35] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c349 := h 348 (by decide)
  have h2 : Entails.eval a c346 := h 345 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨27, by decide⟩, false), (⟨50, by decide⟩, true), (⟨20, by decide⟩, true), (⟨6, by decide⟩, false), (⟨38, by decide⟩, true), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨36, by decide⟩, false), (⟨31, by decide⟩, false), (⟨39, by decide⟩, true), (⟨26, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c220, some c446, some c450, some c169, some c2, some c154, some c174, some c227, some c127, some c109, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c220, c446, c450, c169, c2, c154, c174, c227, c127, c109] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c220 := h 219 (by decide)
  have h1 : Entails.eval a c446 := derived446 a h
  have h2 : Entails.eval a c450 := derived450 a h
  have h3 : Entails.eval a c169 := h 168 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c174 := h 173 (by decide)
  have h7 : Entails.eval a c227 := h 226 (by decide)
  have h8 : Entails.eval a c127 := h 126 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c639, some c97, some c39, some c656, some c309, some c103, some c650, some c556, some c375, some c658, some c196, some c659, some c64, some c101, some c98, some c654, some c600, some c47, some c66, some c311, some c299, some c207, some c660, some c34, some c250, some c450, some c495, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c620, c639, c97, c39, c656, c309, c103, c650, c556, c375, c658, c196, c659, c64, c101, c98, c654, c600, c47, c66, c311, c299, c207, c660, c34, c250, c450, c495] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c656 := derived656 a h
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c658 := derived658 a h
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c659 := derived659 a h
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c654 := derived654 a h
  have h17 : Entails.eval a c600 := derived600 a h
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c311 := h 310 (by decide)
  have h21 : Entails.eval a c299 := h 298 (by decide)
  have h22 : Entails.eval a c207 := h 206 (by decide)
  have h23 : Entails.eval a c660 := derived660 a h
  have h24 : Entails.eval a c34 := h 33 (by decide)
  have h25 : Entails.eval a c250 := h 249 (by decide)
  have h26 : Entails.eval a c450 := derived450 a h
  have h27 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c650, some c196, some c656, some c309, some c620, some c103, some c639, some c97, some c556, some c375, some c311, some c299, some c207, some c90, some c67, some c260, some c250, some c101, some c281, some c283, some c34, some c600, some c77, some c495, some c320, some c140, some c165, some c111, some c184, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c650, c196, c656, c309, c620, c103, c639, c97, c556, c375, c311, c299, c207, c90, c67, c260, c250, c101, c281, c283, c34, c600, c77, c495, c320, c140, c165, c111, c184] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c650 := derived650 a h
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c656 := derived656 a h
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c620 := derived620 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c639 := derived639 a h
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c311 := h 310 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c250 := h 249 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c283 := h 282 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  have h21 : Entails.eval a c600 := derived600 a h
  have h22 : Entails.eval a c77 := h 76 (by decide)
  have h23 : Entails.eval a c495 := derived495 a h
  have h24 : Entails.eval a c320 := h 319 (by decide)
  have h25 : Entails.eval a c140 := h 139 (by decide)
  have h26 : Entails.eval a c165 := h 164 (by decide)
  have h27 : Entails.eval a c111 := h 110 (by decide)
  have h28 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c103, some c650, some c639, some c556, some c662, some c47, some c203, some c98, some c247, some c90, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c620, c103, c650, c639, c556, c662, c47, c203, c98, c247, c90] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c650 := derived650 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c662 := derived662 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c661, some c620, some c639, some c97, some c39, some c656, some c309, some c650, some c196, some c663, some c216, some c28, some c654, some c207, some c64, some c305, some c350, some c346, some c261, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c661, c620, c639, c97, c39, c656, c309, c650, c196, c663, c216, c28, c654, c207, c64, c305, c350, c346, c261] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c661 := derived661 a h
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c656 := derived656 a h
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c663 := derived663 a h
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c654 := derived654 a h
  have h13 : Entails.eval a c207 := h 206 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c350 := h 349 (by decide)
  have h17 : Entails.eval a c346 := h 345 (by decide)
  have h18 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c656, some c309, some c620, some c103, some c650, some c639, some c97, some c556, some c39, some c661, some c664, some c252, some c216, some c28, some c654, some c70, some c90, some c64, some c299, some c47, some c455, some c244, some c24, some c66, some c34, some c319, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c656, c309, c620, c103, c650, c639, c97, c556, c39, c661, c664, c252, c216, c28, c654, c70, c90, c64, c299, c47, c455, c244, c24, c66, c34, c319] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c656 := derived656 a h
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c639 := derived639 a h
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c661 := derived661 a h
  have h10 : Entails.eval a c664 := derived664 a h
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c654 := derived654 a h
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c90 := h 89 (by decide)
  have h17 : Entails.eval a c64 := h 63 (by decide)
  have h18 : Entails.eval a c299 := h 298 (by decide)
  have h19 : Entails.eval a c47 := h 46 (by decide)
  have h20 : Entails.eval a c455 := derived455 a h
  have h21 : Entails.eval a c244 := h 243 (by decide)
  have h22 : Entails.eval a c24 := h 23 (by decide)
  have h23 : Entails.eval a c66 := h 65 (by decide)
  have h24 : Entails.eval a c34 := h 33 (by decide)
  have h25 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c650, some c620, some c639, some c97, some c556, some c103, some c656, some c309, some c665, some c344, some c40, some c196, some c98, some c252, some c90, some c427, some c299, some c339, some c35, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c650, c620, c639, c97, c556, c103, c656, c309, c665, c344, c40, c196, c98, c252, c90, c427, c299, c339, c35] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c650 := derived650 a h
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c656 := derived656 a h
  have h7 : Entails.eval a c309 := h 308 (by decide)
  have h8 : Entails.eval a c665 := derived665 a h
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c427 := derived427 a h
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c339 := h 338 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨26, by decide⟩, true), (⟨31, by decide⟩, false), (⟨39, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c650, some c344, some c196, some c639, some c40, some c20, some c98, some c620, some c97, some c556, some c375, some c339, some c352, some c90, some c431, some c271, some c499, some c305, some c153, some c197, some c286, some c24, some c482, some c77, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c650, c344, c196, c639, c40, c20, c98, c620, c97, c556, c375, c339, c352, c90, c431, c271, c499, c305, c153, c197, c286, c24, c482, c77] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c650 := derived650 a h
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c620 := derived620 a h
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c431 := derived431 a h
  have h15 : Entails.eval a c271 := h 270 (by decide)
  have h16 : Entails.eval a c499 := derived499 a h
  have h17 : Entails.eval a c305 := h 304 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c197 := h 196 (by decide)
  have h20 : Entails.eval a c286 := h 285 (by decide)
  have h21 : Entails.eval a c24 := h 23 (by decide)
  have h22 : Entails.eval a c482 := derived482 a h
  have h23 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, false), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c98, some c70, some c196, some c20, some c299, some c312, some c90, some c271, some c499, some c342, some c345, some c178, some c189, some c118, some c274, some c149, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c40, c98, c70, c196, c20, c299, c312, c90, c271, c499, c342, c345, c178, c189, c118, c274, c149] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c299 := h 298 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c499 := derived499 a h
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c345 := h 344 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c189 := h 188 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c274 := h 273 (by decide)
  have h16 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨39, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c650, some c344, some c196, some c639, some c40, some c20, some c98, some c620, some c556, some c375, some c668, some c267, some c339, some c352, some c667, some c90, some c431, some c271, some c309, some c499, some c305, some c199, some c178, some c198, some c256, some c123, some c26, some c108, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c650, c344, c196, c639, c40, c20, c98, c620, c556, c375, c668, c267, c339, c352, c667, c90, c431, c271, c309, c499, c305, c199, c178, c198, c256, c123, c26, c108] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c650 := derived650 a h
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c620 := derived620 a h
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c668 := derived668 a h
  have h11 : Entails.eval a c267 := h 266 (by decide)
  have h12 : Entails.eval a c339 := h 338 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c667 := derived667 a h
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c431 := derived431 a h
  have h17 : Entails.eval a c271 := h 270 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  have h19 : Entails.eval a c499 := derived499 a h
  have h20 : Entails.eval a c305 := h 304 (by decide)
  have h21 : Entails.eval a c199 := h 198 (by decide)
  have h22 : Entails.eval a c178 := h 177 (by decide)
  have h23 : Entails.eval a c198 := h 197 (by decide)
  have h24 : Entails.eval a c256 := h 255 (by decide)
  have h25 : Entails.eval a c123 := h 122 (by decide)
  have h26 : Entails.eval a c26 := h 25 (by decide)
  have h27 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c666, some c650, some c620, some c639, some c97, some c344, some c40, some c196, some c252, some c669, some c427, some c48, some c309, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c666, c650, c620, c639, c97, c344, c40, c196, c252, c669, c427, c48, c309] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c666 := derived666 a h
  have h1 : Entails.eval a c650 := derived650 a h
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c196 := h 195 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c669 := derived669 a h
  have h10 : Entails.eval a c427 := derived427 a h
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c639, some c97, some c666, some c670, some c60, some c650, some c40, some c196, some c98, some c252, some c64, some c349, some c57, some c213, some c24, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c620, c639, c97, c666, c670, c60, c650, c40, c196, c98, c252, c64, c349, c57, c213, c24] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c666 := derived666 a h
  have h4 : Entails.eval a c670 := derived670 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c650 := derived650 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c252 := h 251 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c213 := h 212 (by decide)
  have h15 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨36, by decide⟩, false), (⟨39, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c64, some c349, some c57, some c213, some c24, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c98, c64, c349, c57, c213, c24] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c349 := h 348 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c64, some c327, some c285, some c81, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c70, c64, c327, c285, c81] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨50, by decide⟩, true), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c673, some c581, some c309, some c60, some c39, some c349, some c346, some c57, some c261, some c305, some c264, some c340, some c495, some c7, some c154, some c327, some c285, some c81, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c97, c673, c581, c309, c60, c39, c349, c346, c57, c261, c305, c264, c340, c495, c7, c154, c327, c285, c81] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c673 := derived673 a h
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  have h12 : Entails.eval a c340 := h 339 (by decide)
  have h13 : Entails.eval a c495 := derived495 a h
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c154 := h 153 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  have h17 : Entails.eval a c285 := h 284 (by decide)
  have h18 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c235, some c81, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c285, c235, c81] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c235 := h 234 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c671, some c620, some c639, some c97, some c666, some c670, some c60, some c39, some c650, some c556, some c375, some c252, some c672, some c49, some c309, some c581, some c571, some c673, some c674, some c220, some c254, some c258, some c657, some c446, some c197, some c348, some c305, some c200, some c26, some c191, some c299, some c675, some c358, some c281, some c283, some c80, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c671, c620, c639, c97, c666, c670, c60, c39, c650, c556, c375, c252, c672, c49, c309, c581, c571, c673, c674, c220, c254, c258, c657, c446, c197, c348, c305, c200, c26, c191, c299, c675, c358, c281, c283, c80] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c671 := derived671 a h
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c670 := derived670 a h
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c650 := derived650 a h
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c672 := derived672 a h
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c309 := h 308 (by decide)
  have h15 : Entails.eval a c581 := derived581 a h
  have h16 : Entails.eval a c571 := derived571 a h
  have h17 : Entails.eval a c673 := derived673 a h
  have h18 : Entails.eval a c674 := derived674 a h
  have h19 : Entails.eval a c220 := h 219 (by decide)
  have h20 : Entails.eval a c254 := h 253 (by decide)
  have h21 : Entails.eval a c258 := h 257 (by decide)
  have h22 : Entails.eval a c657 := derived657 a h
  have h23 : Entails.eval a c446 := derived446 a h
  have h24 : Entails.eval a c197 := h 196 (by decide)
  have h25 : Entails.eval a c348 := h 347 (by decide)
  have h26 : Entails.eval a c305 := h 304 (by decide)
  have h27 : Entails.eval a c200 := h 199 (by decide)
  have h28 : Entails.eval a c26 := h 25 (by decide)
  have h29 : Entails.eval a c191 := h 190 (by decide)
  have h30 : Entails.eval a c299 := h 298 (by decide)
  have h31 : Entails.eval a c675 := derived675 a h
  have h32 : Entails.eval a c358 := h 357 (by decide)
  have h33 : Entails.eval a c281 := h 280 (by decide)
  have h34 : Entails.eval a c283 := h 282 (by decide)
  have h35 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨50, by decide⟩, true), (⟨34, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨31, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c18, some c309, some c2, some c129, some c149, some c169, some c107, some c7, some c257, some c66, some c197, some c318, some c275, some c80, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c18, c309, c2, c129, c149, c169, c107, c7, c257, c66, c197, c318, c275, c80] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c18 := h 17 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c257 := h 256 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c275 := h 274 (by decide)
  have h13 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c620, some c639, some c97, some c666, some c670, some c671, some c650, some c49, some c673, some c309, some c60, some c39, some c375, some c446, some c336, some c677, some c154, some c563, some c285, some c353, some c81, some c320, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c556, c620, c639, c97, c666, c670, c671, c650, c49, c673, c309, c60, c39, c375, c446, c336, c677, c154, c563, c285, c353, c81, c320] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c620 := derived620 a h
  have h2 : Entails.eval a c639 := derived639 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c666 := derived666 a h
  have h5 : Entails.eval a c670 := derived670 a h
  have h6 : Entails.eval a c671 := derived671 a h
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c673 := derived673 a h
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c375 := h 374 (by decide)
  have h14 : Entails.eval a c446 := derived446 a h
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c677 := derived677 a h
  have h17 : Entails.eval a c154 := h 153 (by decide)
  have h18 : Entails.eval a c563 := derived563 a h
  have h19 : Entails.eval a c285 := h 284 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c81 := h 80 (by decide)
  have h22 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c581, some c309, some c97, some c60, some c39, some c349, some c346, some c674, some c261, some c376, some c305, some c207, some c264, some c17, some c351, some c210, some c26, some c35, some c67, some c281, some c283, some c80, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c49, c581, c309, c97, c60, c39, c349, c346, c674, c261, c376, c305, c207, c264, c17, c351, c210, c26, c35, c67, c281, c283, c80] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c581 := derived581 a h
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c674 := derived674 a h
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c305 := h 304 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c264 := h 263 (by decide)
  have h14 : Entails.eval a c17 := h 16 (by decide)
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c26 := h 25 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c67 := h 66 (by decide)
  have h20 : Entails.eval a c281 := h 280 (by decide)
  have h21 : Entails.eval a c283 := h 282 (by decide)
  have h22 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c556, some c620, some c639, some c650, some c666, some c670, some c671, some c676, some c679, some c678, some c220, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c375, c556, c620, c639, c650, c666, c670, c671, c676, c679, c678, c220] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c666 := derived666 a h
  have h6 : Entails.eval a c670 := derived670 a h
  have h7 : Entails.eval a c671 := derived671 a h
  have h8 : Entails.eval a c676 := derived676 a h
  have h9 : Entails.eval a c679 := derived679 a h
  have h10 : Entails.eval a c678 := derived678 a h
  have h11 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived680

end CochromaticTwenty.Certificates.B16_8_2
