import MerLeanExperiment.Certificates.B16_8_1.Steps0300_0399

/-! Generated from the actual pinned b16_8_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c689 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c647, some c83, some c659, some c666, some c670, some c285, some c680, some c280, some c685, some c687, some c72, some c76, some c277, some c664, some c653, some c24, some c688, some c112, some c265, some c266, some c264, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c647, c83, c659, c666, c670, c285, c680, c280, c685, c687, c72, c76, c277, c664, c653, c24, c688, c112, c265, c266, c264] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c647 := derived647 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c666 := derived666 a h
  have h4 : Entails.eval a c670 := derived670 a h
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c680 := derived680 a h
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c685 := derived685 a h
  have h9 : Entails.eval a c687 := derived687 a h
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c277 := h 276 (by decide)
  have h13 : Entails.eval a c664 := derived664 a h
  have h14 : Entails.eval a c653 := derived653 a h
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c688 := derived688 a h
  have h17 : Entails.eval a c112 := h 111 (by decide)
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c266 := h 265 (by decide)
  have h20 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c647, some c83, some c689, some c61, some c549, some c273, some c267, some c112, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c647, c83, c689, c61, c549, c273, c267, c112] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c647 := derived647 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c549 := derived549 a h
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c647, some c83, some c689, some c52, some c277, some c278, some c690, some c62, some c87, some c77, some c61, some c263, some c109, some c276, some c268, some c558, some c261, some c113, some c282, some c17, some c124, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c647, c83, c689, c52, c277, c278, c690, c62, c87, c77, c61, c263, c109, c276, c268, c558, c261, c113, c282, c17, c124] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c647 := derived647 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c690 := derived690 a h
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c276 := h 275 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c558 := derived558 a h
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c282 := h 281 (by decide)
  have h19 : Entails.eval a c17 := h 16 (by decide)
  have h20 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c689, some c647, some c83, some c690, some c62, some c87, some c691, some c564, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c689, c647, c83, c690, c62, c87, c691, c564] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c689 := derived689 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c690 := derived690 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c691 := derived691 a h
  have h7 : Entails.eval a c564 := derived564 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c692, some c647, some c83, some c689, some c52, some c277, some c278, some c279, some c564, some c87, some c653, some c651, some c24, some c4, some c127, some c131, some c135, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c692, c647, c83, c689, c52, c277, c278, c279, c564, c87, c653, c651, c24, c4, c127, c131, c135] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c692 := derived692 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c689 := derived689 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c277 := h 276 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c564 := derived564 a h
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c653 := derived653 a h
  have h11 : Entails.eval a c651 := derived651 a h
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c277, some c278, some c55, some c76, some c653, some c542, some c688, some c235, some c24, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c277, c278, c55, c76, c653, c542, c688, c235, c24] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c277 := h 276 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c653 := derived653 a h
  have h5 : Entails.eval a c542 := derived542 a h
  have h6 : Entails.eval a c688 := derived688 a h
  have h7 : Entails.eval a c235 := h 234 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c647, some c83, some c689, some c52, some c61, some c278, some c277, some c692, some c693, some c694, some c87, some c73, some c77, some c664, some c688, some c24, some c199, some c198, some c35, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c647, c83, c689, c52, c61, c278, c277, c692, c693, c694, c87, c73, c77, c664, c688, c24, c199, c198, c35] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c647 := derived647 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c692 := derived692 a h
  have h8 : Entails.eval a c693 := derived693 a h
  have h9 : Entails.eval a c694 := derived694 a h
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c77 := h 76 (by decide)
  have h13 : Entails.eval a c664 := derived664 a h
  have h14 : Entails.eval a c688 := derived688 a h
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c198 := h 197 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c87, some c695, some c647, some c83, some c689, some c52, some c61, some c610, some c549, some c273, some c267, some c105, some c50, some c283, some c688, some c77, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c87, c695, c647, c83, c689, c52, c61, c610, c549, c273, c267, c105, c50, c283, c688, c77] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c87 := h 86 (by decide)
  have h1 : Entails.eval a c695 := derived695 a h
  have h2 : Entails.eval a c647 := derived647 a h
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c689 := derived689 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c610 := derived610 a h
  have h8 : Entails.eval a c549 := derived549 a h
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c283 := h 282 (by decide)
  have h14 : Entails.eval a c688 := derived688 a h
  have h15 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨10, by decide⟩, true), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c5, some c109, some c273, some c267, some c114, some c256, some c276, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c3, c5, c109, c273, c267, c114, c256, c276] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c695, some c647, some c83, some c689, some c52, some c61, some c87, some c696, some c364, some c287, some c537, some c283, some c73, some c56, some c679, some c697, some c50, some c269, some c268, some c109, some c261, some c136, some c272, some c129, some c114, some c17, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c695, c647, c83, c689, c52, c61, c87, c696, c364, c287, c537, c283, c73, c56, c679, c697, c50, c269, c268, c109, c261, c136, c272, c129, c114, c17] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c695 := derived695 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c689 := derived689 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c696 := derived696 a h
  have h8 : Entails.eval a c364 := derived364 a h
  have h9 : Entails.eval a c287 := h 286 (by decide)
  have h10 : Entails.eval a c537 := derived537 a h
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c73 := h 72 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c679 := derived679 a h
  have h15 : Entails.eval a c697 := derived697 a h
  have h16 : Entails.eval a c50 := h 49 (by decide)
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c109 := h 108 (by decide)
  have h20 : Entails.eval a c261 := h 260 (by decide)
  have h21 : Entails.eval a c136 := h 135 (by decide)
  have h22 : Entails.eval a c272 := h 271 (by decide)
  have h23 : Entails.eval a c129 := h 128 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c695, some c647, some c83, some c689, some c52, some c61, some c698, some c55, some c549, some c273, some c267, some c105, some c50, some c282, some c283, some c256, some c276, some c652, some c114, some c135, some c5, some c679, some c73, some c127, some c4, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c695, c647, c83, c689, c52, c61, c698, c55, c549, c273, c267, c105, c50, c282, c283, c256, c276, c652, c114, c135, c5, c679, c73, c127, c4] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c695 := derived695 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c689 := derived689 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c698 := derived698 a h
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c549 := derived549 a h
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  have h15 : Entails.eval a c256 := h 255 (by decide)
  have h16 : Entails.eval a c276 := h 275 (by decide)
  have h17 : Entails.eval a c652 := derived652 a h
  have h18 : Entails.eval a c114 := h 113 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  have h20 : Entails.eval a c5 := h 4 (by decide)
  have h21 : Entails.eval a c679 := derived679 a h
  have h22 : Entails.eval a c73 := h 72 (by decide)
  have h23 : Entails.eval a c127 := h 126 (by decide)
  have h24 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c695, some c647, some c83, some c689, some c52, some c61, some c549, some c273, some c267, some c105, some c50, some c285, some c282, some c286, some c73, some c256, some c4, some c276, some c127, some c114, some c135, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c699, c695, c647, c83, c689, c52, c61, c549, c273, c267, c105, c50, c285, c282, c286, c73, c256, c4, c276, c127, c114, c135] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c695 := derived695 a h
  have h2 : Entails.eval a c647 := derived647 a h
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c689 := derived689 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c549 := derived549 a h
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c256 := h 255 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c276 := h 275 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  have h20 : Entails.eval a c114 := h 113 (by decide)
  have h21 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨46, by decide⟩, true), (⟨9, by decide⟩, false), (⟨49, by decide⟩, true), (⟨44, by decide⟩, false), (⟨43, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c52, some c3, some c362, some c531, some c276, some c268, some c133, some c256, some c118, some c287, some c282, some c137, some c124, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c62, c52, c3, c362, c531, c276, c268, c133, c256, c118, c287, c282, c137, c124] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c362 := derived362 a h
  have h4 : Entails.eval a c531 := derived531 a h
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c287 := h 286 (by decide)
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c137 := h 136 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨48, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c136, some c105, some c521, some c272, some c57, some c111, some c17, some c119, some c302, some c304, some c145, some c161, some c163, some c331, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c136, c105, c521, c272, c57, c111, c17, c119, c302, c304, c145, c161, c163, c331] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c521 := derived521 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c302 := derived302 a h
  have h9 : Entails.eval a c304 := derived304 a h
  have h10 : Entails.eval a c145 := h 144 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c331 := derived331 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c695, some c647, some c83, some c689, some c52, some c61, some c699, some c700, some c62, some c87, some c701, some c50, some c268, some c332, some c9, some c702, some c285, some c286, some c73, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c695, c647, c83, c689, c52, c61, c699, c700, c62, c87, c701, c50, c268, c332, c9, c702, c285, c286, c73] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c695 := derived695 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c689 := derived689 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c699 := derived699 a h
  have h7 : Entails.eval a c700 := derived700 a h
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c701 := derived701 a h
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c332 := derived332 a h
  have h14 : Entails.eval a c9 := h 8 (by decide)
  have h15 : Entails.eval a c702 := derived702 a h
  have h16 : Entails.eval a c285 := h 284 (by decide)
  have h17 : Entails.eval a c286 := h 285 (by decide)
  have h18 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨46, by decide⟩, true), (⟨9, by decide⟩, true), (⟨49, by decide⟩, true), (⟨51, by decide⟩, false), (⟨44, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c268, some c122, some c282, some c283, some c123, some c73, some c285, some c610, some c261, some c679, some c272, some c17, some c114, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c104, c268, c122, c282, c283, c123, c73, c285, c610, c261, c679, c272, c17, c114] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c122 := h 121 (by decide)
  have h3 : Entails.eval a c282 := h 281 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c610 := derived610 a h
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c679 := derived679 a h
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c647, some c83, some c689, some c61, some c52, some c695, some c703, some c690, some c62, some c87, some c704, some c8, some c537, some c9, some c118, some c521, some c540, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c647, c83, c689, c61, c52, c695, c703, c690, c62, c87, c704, c8, c537, c9, c118, c521, c540] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c647 := derived647 a h
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c695 := derived695 a h
  have h6 : Entails.eval a c703 := derived703 a h
  have h7 : Entails.eval a c690 := derived690 a h
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c704 := derived704 a h
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c537 := derived537 a h
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c521 := derived521 a h
  have h16 : Entails.eval a c540 := derived540 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨48, by decide⟩, true), (⟨51, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c521, some c257, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c521, c257] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c521 := derived521 a h
  have h1 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c7, some c127, some c10, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c705, c7, c127, c10] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨44, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c64, some c55, some c276, some c272, some c300, some c706, some c282, some c283, some c285, some c630, some c69, some c84, some c707, some c278, some c62, some c112, some c650, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c705, c86, c85, c64, c55, c276, c272, c300, c706, c282, c283, c285, c630, c69, c84, c707, c278, c62, c112, c650] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c300 := derived300 a h
  have h8 : Entails.eval a c706 := derived706 a h
  have h9 : Entails.eval a c282 := h 281 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c630 := derived630 a h
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  have h15 : Entails.eval a c707 := derived707 a h
  have h16 : Entails.eval a c278 := h 277 (by decide)
  have h17 : Entails.eval a c62 := h 61 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c650 := derived650 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨10, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c277, some c705, some c86, some c85, some c630, some c74, some c707, some c279, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c277, c705, c86, c85, c630, c74, c707, c279] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c277 := h 276 (by decide)
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c630 := derived630 a h
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c707 := derived707 a h
  have h7 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c708, some c273, some c267, some c104, some c112, some c278, some c277, some c709, some c282, some c540, some c59, some c81, some c76, some c77, some c279, some c707, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c705, c86, c85, c708, c273, c267, c104, c112, c278, c277, c709, c282, c540, c59, c81, c76, c77, c279, c707] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c708 := derived708 a h
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c278 := h 277 (by decide)
  have h9 : Entails.eval a c277 := h 276 (by decide)
  have h10 : Entails.eval a c709 := derived709 a h
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c540 := derived540 a h
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  have h16 : Entails.eval a c77 := h 76 (by decide)
  have h17 : Entails.eval a c279 := h 278 (by decide)
  have h18 : Entails.eval a c707 := derived707 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨47, by decide⟩, false), (⟨3, by decide⟩, true), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c289, some c265, some c62, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c104, c289, c265, c62] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c289 := derived289 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨56, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c279, some c76, some c81, some c579, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c705, c86, c279, c76, c81, c579] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c279 := h 278 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c579 := derived579 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨10, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c7, some c85, some c117, some c138, some c10, some c115, some c600, some c65, some c275, some c257, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c705, c7, c85, c117, c138, c10, c115, c600, c65, c275, c257] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c600 := derived600 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨56, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c7, some c321, some c712, some c104, some c713, some c711, some c265, some c6, some c115, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c705, c86, c7, c321, c712, c104, c713, c711, c265, c6, c115] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c321 := derived321 a h
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c713 := derived713 a h
  have h7 : Entails.eval a c711 := derived711 a h
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c6 := h 5 (by decide)
  have h10 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c710, some c705, some c521, some c714, some c122, some c124, some c712, some c522, some c107, some c16, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c710, c705, c521, c714, c122, c124, c712, c522, c107, c16] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c710 := derived710 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c521 := derived521 a h
  have h3 : Entails.eval a c714 := derived714 a h
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c712 := derived712 a h
  have h7 : Entails.eval a c522 := derived522 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c200, some c36, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c198, c200, c36] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨47, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c269, some c513, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c269, c513] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c513 := derived513 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c710, some c715, some c282, some c283, some c54, some c630, some c74, some c84, some c285, some c321, some c260, some c717, some c62, some c270, some c265, some c112, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c705, c86, c85, c710, c715, c282, c283, c54, c630, c74, c84, c285, c321, c260, c717, c62, c270, c265, c112] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c710 := derived710 a h
  have h4 : Entails.eval a c715 := derived715 a h
  have h5 : Entails.eval a c282 := h 281 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c630 := derived630 a h
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c321 := derived321 a h
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c717 := derived717 a h
  have h15 : Entails.eval a c62 := h 61 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c265 := h 264 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c52, some c705, some c85, some c54, some c270, some c275, some c86, some c72, some c286, some c285, some c75, some c707, some c112, some c265, some c260, some c267, some c300, some c314, some c312, some c26, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c718, c52, c705, c85, c54, c270, c275, c86, c72, c286, c285, c75, c707, c112, c265, c260, c267, c300, c314, c312, c26] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c275 := h 274 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c72 := h 71 (by decide)
  have h9 : Entails.eval a c286 := h 285 (by decide)
  have h10 : Entails.eval a c285 := h 284 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c707 := derived707 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c265 := h 264 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c300 := derived300 a h
  have h18 : Entails.eval a c314 := derived314 a h
  have h19 : Entails.eval a c312 := derived312 a h
  have h20 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c705, some c86, some c72, some c52, some c85, some c54, some c270, some c719, some c363, some c105, some c281, some c279, some c75, some c707, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c718, c705, c86, c72, c52, c85, c54, c270, c719, c363, c105, c281, c279, c75, c707] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c719 := derived719 a h
  have h9 : Entails.eval a c363 := derived363 a h
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c279 := h 278 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c707 := derived707 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c397, some c125, some c127, some c138, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c397, c125, c127, c138] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c397 := derived397 a h
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c720, some c718, some c705, some c86, some c72, some c85, some c7, some c721, some c288, some c712, some c714, some c540, some c104, some c64, some c267, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c720, c718, c705, c86, c72, c85, c7, c721, c288, c712, c714, c540, c104, c64, c267] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c720 := derived720 a h
  have h1 : Entails.eval a c718 := derived718 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c721 := derived721 a h
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c712 := derived712 a h
  have h10 : Entails.eval a c714 := derived714 a h
  have h11 : Entails.eval a c540 := derived540 a h
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c705, some c86, some c72, some c52, some c85, some c722, some c122, some c105, some c281, some c279, some c485, some c271, some c64, some c260, some c273, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c718, c705, c86, c72, c52, c85, c722, c122, c105, c281, c279, c485, c271, c64, c260, c273] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c722 := derived722 a h
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c279 := h 278 (by decide)
  have h11 : Entails.eval a c485 := derived485 a h
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨46, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c267, some c112, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c273, c267, c112] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨10, by decide⟩, true), (⟨52, by decide⟩, true), (⟨55, by decide⟩, true), (⟨54, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c724, some c260, some c717, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c724, c260, c717] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c724 := derived724 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c717 := derived717 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c705, some c86, some c72, some c723, some c285, some c286, some c52, some c85, some c725, some c64, some c275, some c270, some c300, some c112, some c314, some c312, some c26, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c718, c705, c86, c72, c723, c285, c286, c52, c85, c725, c64, c275, c270, c300, c112, c314, c312, c26] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c723 := derived723 a h
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c286 := h 285 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c725 := derived725 a h
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c275 := h 274 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c300 := derived300 a h
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c314 := derived314 a h
  have h16 : Entails.eval a c312 := derived312 a h
  have h17 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c705, some c86, some c72, some c723, some c285, some c726, some c7, some c721, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c718, c705, c86, c72, c723, c285, c726, c7, c721] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c723 := derived723 a h
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c726 := derived726 a h
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c721 := derived721 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨50, by decide⟩, true), (⟨42, by decide⟩, true), (⟨43, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c364, some c266, some c257, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c104, c364, c266, c257] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c364 := derived364 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c727, some c84, some c718, some c705, some c85, some c7, some c6, some c106, some c125, some c600, some c602, some c728, some c280, some c712, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c727, c84, c718, c705, c85, c7, c6, c106, c125, c600, c602, c728, c280, c712] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c727 := derived727 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c718 := derived718 a h
  have h3 : Entails.eval a c705 := derived705 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c600 := derived600 a h
  have h10 : Entails.eval a c602 := derived602 a h
  have h11 : Entails.eval a c728 := derived728 a h
  have h12 : Entails.eval a c280 := h 279 (by decide)
  have h13 : Entails.eval a c712 := derived712 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c712, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c280, c712] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c729, some c727, some c718, some c705, some c85, some c730, some c597, some c598, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c729, c727, c718, c705, c85, c730, c597, c598] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c729 := derived729 a h
  have h1 : Entails.eval a c727 := derived727 a h
  have h2 : Entails.eval a c718 := derived718 a h
  have h3 : Entails.eval a c705 := derived705 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c730 := derived730 a h
  have h6 : Entails.eval a c597 := derived597 a h
  have h7 : Entails.eval a c598 := derived598 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c731, some c104, some c297, some c729, some c727, some c84, some c705, some c85, some c600, some c265, some c114, some c67, some c65, some c327, some c559, some c16, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c718, c731, c104, c297, c729, c727, c84, c705, c85, c600, c265, c114, c67, c65, c327, c559, c16] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c731 := derived731 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c297 := derived297 a h
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c727 := derived727 a h
  have h6 : Entails.eval a c84 := h 83 (by decide)
  have h7 : Entails.eval a c705 := derived705 a h
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c600 := derived600 a h
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c327 := derived327 a h
  have h15 : Entails.eval a c559 := derived559 a h
  have h16 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c729, some c727, some c718, some c705, some c86, some c85, some c104, some c297, some c732, some c258, some c106, some c267, some c64, some c66, some c485, some c13, some c114, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c731, c729, c727, c718, c705, c86, c85, c104, c297, c732, c258, c106, c267, c64, c66, c485, c13, c114] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c727 := derived727 a h
  have h3 : Entails.eval a c718 := derived718 a h
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c297 := derived297 a h
  have h9 : Entails.eval a c732 := derived732 a h
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c485 := derived485 a h
  have h16 : Entails.eval a c13 := h 12 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c729, some c727, some c718, some c705, some c86, some c85, some c258, some c106, some c724, some c64, some c485, some c276, some c114, some c66, some c13, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c731, c729, c727, c718, c705, c86, c85, c258, c106, c724, c64, c485, c276, c114, c66, c13] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c729 := derived729 a h
  have h2 : Entails.eval a c727 := derived727 a h
  have h3 : Entails.eval a c718 := derived718 a h
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c724 := derived724 a h
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c485 := derived485 a h
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c114 := h 113 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c718, some c727, some c84, some c729, some c731, some c733, some c734, some c600, some c112, some c297, some c265, some c114, some c67, some c56, some c16, some c397, some c563, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c705, c86, c85, c718, c727, c84, c729, c731, c733, c734, c600, c112, c297, c265, c114, c67, c56, c16, c397, c563] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c718 := derived718 a h
  have h4 : Entails.eval a c727 := derived727 a h
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c729 := derived729 a h
  have h7 : Entails.eval a c731 := derived731 a h
  have h8 : Entails.eval a c733 := derived733 a h
  have h9 : Entails.eval a c734 := derived734 a h
  have h10 : Entails.eval a c600 := derived600 a h
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c297 := derived297 a h
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c67 := h 66 (by decide)
  have h16 : Entails.eval a c56 := h 55 (by decide)
  have h17 : Entails.eval a c16 := h 15 (by decide)
  have h18 : Entails.eval a c397 := derived397 a h
  have h19 : Entails.eval a c563 := derived563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨42, by decide⟩, true), (⟨3, by decide⟩, false), (⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c85, some c730, some c601, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c705, c85, c730, c601] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c730 := derived730 a h
  have h3 : Entails.eval a c601 := derived601 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c85, some c84, some c600, some c736, some c735, some c125, some c133, some c1, some c560, some c557, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c705, c85, c84, c600, c736, c735, c125, c133, c1, c560, c557] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c736 := derived736 a h
  have h5 : Entails.eval a c735 := derived735 a h
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c560 := derived560 a h
  have h10 : Entails.eval a c557 := derived557 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c705, some c85, some c84, some c600, some c737, some c2, some c135, some c557, some c114, some c275, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c735, c705, c85, c84, c600, c737, c2, c135, c557, c114, c275] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c600 := derived600 a h
  have h5 : Entails.eval a c737 := derived737 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c557 := derived557 a h
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨51, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c286, some c125, some c127, some c132, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c285, c286, c125, c127, c132] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c738, some c72, some c735, some c85, some c739, some c105, some c270, some c271, some c64, some c273, some c117, some c132, some c136, some c352, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c705, c86, c738, c72, c735, c85, c739, c105, c270, c271, c64, c273, c117, c132, c136, c352] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c738 := derived738 a h
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c735 := derived735 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c739 := derived739 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c273 := h 272 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c136 := h 135 (by decide)
  have h15 : Entails.eval a c352 := derived352 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨43, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c270, some c64, some c59, some c273, some c445, some c266, some c111, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c705, c86, c85, c270, c64, c59, c273, c445, c266, c111] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c445 := derived445 a h
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c705, some c85, some c740, some c2, some c135, some c741, some c114, some c275, some c266, some c59, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c735, c705, c85, c740, c2, c135, c741, c114, c275, c266, c59] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c740 := derived740 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c741 := derived741 a h
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c275 := h 274 (by decide)
  have h9 : Entails.eval a c266 := h 265 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c742, some c106, some c133, some c292, some c52, some c705, some c85, some c736, some c114, some c297, some c258, some c276, some c59, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c735, c742, c106, c133, c292, c52, c705, c85, c736, c114, c297, c258, c276, c59] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c742 := derived742 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c292 := derived292 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c705 := derived705 a h
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c736 := derived736 a h
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c297 := derived297 a h
  have h11 : Entails.eval a c258 := h 257 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c64, some c376, some c59, some c269, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c705, c86, c85, c64, c376, c59, c269] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c376 := derived376 a h
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c705, some c85, some c742, some c52, some c292, some c743, some c744, some c485, some c730, some c597, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c735, c705, c85, c742, c52, c292, c743, c744, c485, c730, c597] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c742 := derived742 a h
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c292 := derived292 a h
  have h6 : Entails.eval a c743 := derived743 a h
  have h7 : Entails.eval a c744 := derived744 a h
  have h8 : Entails.eval a c485 := derived485 a h
  have h9 : Entails.eval a c730 := derived730 a h
  have h10 : Entails.eval a c597 := derived597 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨45, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c287, some c282, some c124, some c540, some c133, some c135, some c115, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c287, c282, c124, c540, c133, c135, c115] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c287 := h 286 (by decide)
  have h1 : Entails.eval a c282 := h 281 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c540 := derived540 a h
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c85, some c630, some c84, some c86, some c74, some c69, some c651, some c716, some c24, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c705, c85, c630, c84, c86, c74, c69, c651, c716, c24] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c630 := derived630 a h
  have h3 : Entails.eval a c84 := h 83 (by decide)
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c651 := derived651 a h
  have h8 : Entails.eval a c716 := derived716 a h
  have h9 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨51, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c705, some c86, some c85, some c630, some c74, some c747, some c2, some c4, some c556, some c363, some c283, some c285, some c127, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c735, c705, c86, c85, c630, c74, c747, c2, c4, c556, c363, c283, c285, c127] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c630 := derived630 a h
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c747 := derived747 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c363 := derived363 a h
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c745, some c748, some c287, some c282, some c124, some c135, some c105, some c705, some c86, some c85, some c746, some c64, some c273, some c274, some c339, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c735, c745, c748, c287, c282, c124, c135, c105, c705, c86, c85, c746, c64, c273, c274, c339] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c745 := derived745 a h
  have h2 : Entails.eval a c748 := derived748 a h
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c705 := derived705 a h
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c746 := derived746 a h
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c273 := h 272 (by decide)
  have h14 : Entails.eval a c274 := h 273 (by decide)
  have h15 : Entails.eval a c339 := derived339 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c705, some c86, some c85, some c745, some c748, some c287, some c282, some c105, some c124, some c133, some c135, some c749, some c270, some c271, some c64, some c376, some c273, some c352, some c117, some c136, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c735, c705, c86, c85, c745, c748, c287, c282, c105, c124, c133, c135, c749, c270, c271, c64, c376, c273, c352, c117, c136] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c705 := derived705 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c745 := derived745 a h
  have h5 : Entails.eval a c748 := derived748 a h
  have h6 : Entails.eval a c287 := h 286 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c749 := derived749 a h
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c376 := derived376 a h
  have h17 : Entails.eval a c273 := h 272 (by decide)
  have h18 : Entails.eval a c352 := derived352 a h
  have h19 : Entails.eval a c117 := h 116 (by decide)
  have h20 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨50, by decide⟩, true), (⟨56, by decide⟩, true), (⟨46, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c750, some c321, some c713, some c730, some c289, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c750, c321, c713, c730, c289] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c321 := derived321 a h
  have h2 : Entails.eval a c713 := derived713 a h
  have h3 : Entails.eval a c730 := derived730 a h
  have h4 : Entails.eval a c289 := derived289 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨45, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c64, some c54, some c750, some c287, some c282, some c751, some c273, some c267, some c255, some c59, some c277, some c730, some c81, some c707, some c77, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c705, c86, c85, c64, c54, c750, c287, c282, c751, c273, c267, c255, c59, c277, c730, c81, c707, c77] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c750 := derived750 a h
  have h6 : Entails.eval a c287 := h 286 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c751 := derived751 a h
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c255 := h 254 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c277 := h 276 (by decide)
  have h14 : Entails.eval a c730 := derived730 a h
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c707 := derived707 a h
  have h17 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c750, some c7, some c721, some c403, some c604, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c705, c750, c7, c721, c403, c604] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c750 := derived750 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c721 := derived721 a h
  have h4 : Entails.eval a c403 := derived403 a h
  have h5 : Entails.eval a c604 := derived604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c273, some c267, some c255, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c273, c267, c255] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c273 := h 272 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c86, some c85, some c54, some c64, some c752, some c753, some c730, some c284, some c288, some c754, some c751, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c705, c86, c85, c54, c64, c752, c753, c730, c284, c288, c754, c751] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c752 := derived752 a h
  have h6 : Entails.eval a c753 := derived753 a h
  have h7 : Entails.eval a c730 := derived730 a h
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c288 := h 287 (by decide)
  have h10 : Entails.eval a c754 := derived754 a h
  have h11 : Entails.eval a c751 := derived751 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨42, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c284, some c288, some c257, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c284, c288, c257] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c284 := h 283 (by decide)
  have h1 : Entails.eval a c288 := h 287 (by decide)
  have h2 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c755, some c270, some c275, some c735, some c705, some c85, some c756, some c599, some c748, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c755, c270, c275, c735, c705, c85, c756, c599, c748] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c755 := derived755 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  have h3 : Entails.eval a c735 := derived735 a h
  have h4 : Entails.eval a c705 := derived705 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c756 := derived756 a h
  have h7 : Entails.eval a c599 := derived599 a h
  have h8 : Entails.eval a c748 := derived748 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨43, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c755, some c270, some c275, some c748, some c282, some c706, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c755, c270, c275, c748, c282, c706] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c755 := derived755 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  have h3 : Entails.eval a c748 := derived748 a h
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c706 := derived706 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c758, some c753, some c730, some c757, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c758, c753, c730, c757] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c758 := derived758 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c730 := derived730 a h
  have h3 : Entails.eval a c757 := derived757 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨52, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c730, some c759, some c705, some c85, some c52, some c597, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c730, c759, c705, c85, c52, c597] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c730 := derived730 a h
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c597 := derived597 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c759, some c755, some c705, some c750, some c7, some c86, some c748, some c287, some c282, some c540, some c115, some c751, some c6, some c62, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c759, c755, c705, c750, c7, c86, c748, c287, c282, c540, c115, c751, c6, c62] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c759 := derived759 a h
  have h1 : Entails.eval a c755 := derived755 a h
  have h2 : Entails.eval a c705 := derived705 a h
  have h3 : Entails.eval a c750 := derived750 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c748 := derived748 a h
  have h7 : Entails.eval a c287 := h 286 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c540 := derived540 a h
  have h10 : Entails.eval a c115 := h 114 (by decide)
  have h11 : Entails.eval a c751 := derived751 a h
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c753, some c760, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c753, c760] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c753 := derived753 a h
  have h1 : Entails.eval a c760 := derived760 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c761, some c762, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c761, c762] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c761 := derived761 a h
  have h1 : Entails.eval a c762 := derived762 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c106, some c52, some c284, some c288, some c51, some c70, some c79, some c13, some c68, some c124, some c279, some c138, some c259, some c130, some c274, some c273, some c140, some c117, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c763, c106, c52, c284, c288, c51, c70, c79, c13, c68, c124, c279, c138, c259, c130, c274, c273, c140, c117] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c288 := h 287 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c279 := h 278 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c274 := h 273 (by decide)
  have h16 : Entails.eval a c273 := h 272 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c764, some c106, some c52, some c363, some c51, some c279, some c280, some c259, some c70, some c274, some c273, some c13, some c124, some c130, some c138, some c140, some c117, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c763, c764, c106, c52, c363, c51, c279, c280, c259, c70, c274, c273, c13, c124, c130, c138, c140, c117] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c764 := derived764 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c363 := derived363 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c279 := h 278 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c259 := h 258 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c273 := h 272 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨56, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, true), (⟨3, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c274, some c269, some c58, some c79, some c76, some c479, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c763, c274, c269, c58, c79, c76, c479] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c479 := derived479 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨1, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c465, some c467, some c147, some c172, some c169, some c90, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c763, c465, c467, c147, c172, c169, c90] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c465 := derived465 a h
  have h2 : Entails.eval a c467 := derived467 a h
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c767, some c123, some c69, some c11, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c767, c123, c69, c11] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c767 := derived767 a h
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c117, some c339, some c138, some c12, some c63, some c768, some c79, some c80, some c76, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c285, c117, c339, c138, c12, c63, c768, c79, c80, c76] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c339 := derived339 a h
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c768 := derived768 a h
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨3, by decide⟩, false), (⟨43, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c341, some c80, some c76, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c79, c341, c80, c76] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c341 := derived341 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c76, some c88, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c74, c76, c88] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c130, some c128, some c142, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c130, c128, c142] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c130 := h 129 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨47, by decide⟩, true), (⟨56, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c772, some c769, some c770, some c140, some c134, some c768, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c285, c772, c769, c770, c140, c134, c768] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c772 := derived772 a h
  have h2 : Entails.eval a c769 := derived769 a h
  have h3 : Entails.eval a c770 := derived770 a h
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c768 := derived768 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨46, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨43, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c285, some c766, some c771, some c773, some c273, some c267, some c58, some c479, some c79, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c763, c285, c766, c771, c773, c273, c267, c58, c479, c79] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c285 := h 284 (by decide)
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c771 := derived771 a h
  have h4 : Entails.eval a c773 := derived773 a h
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c479 := derived479 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨49, by decide⟩, true), (⟨46, by decide⟩, false), (⟨43, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c273, some c267, some c58, some c104, some c292, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c763, c273, c267, c58, c104, c292] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c292 := derived292 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c259, some c775, some c106, some c52, some c292, some c104, some c123, some c269, some c11, some c341, some c74, some c80, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c259, c775, c106, c52, c292, c104, c123, c269, c11, c341, c74, c80] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c775 := derived775 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c292 := derived292 a h
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c341 := derived341 a h
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c106, some c764, some c765, some c285, some c259, some c774, some c280, some c775, some c776, some c50, some c69, some c269, some c11, some c128, some c123, some c339, some c134, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c52, c106, c764, c765, c285, c259, c774, c280, c775, c776, c50, c69, c269, c11, c128, c123, c339, c134] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c764 := derived764 a h
  have h3 : Entails.eval a c765 := derived765 a h
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c774 := derived774 a h
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c775 := derived775 a h
  have h9 : Entails.eval a c776 := derived776 a h
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c69 := h 68 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c339 := derived339 a h
  have h17 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨47, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true), (⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c366, some c136, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c351, c366, c136] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c351 := derived351 a h
  have h1 : Entails.eval a c366 := derived366 a h
  have h2 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c141, some c126, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c137, c141, c126] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨44, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c671, some c510, some c363, some c50, some c69, some c265, some c88, some c345, some c72, some c778, some c123, some c17, some c121, some c779, some c18, some c114, some c109, some c270, some c448, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c763, c671, c510, c363, c50, c69, c265, c88, c345, c72, c778, c123, c17, c121, c779, c18, c114, c109, c270, c448] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c510 := derived510 a h
  have h3 : Entails.eval a c363 := derived363 a h
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c345 := derived345 a h
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c778 := derived778 a h
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c17 := h 16 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c779 := derived779 a h
  have h15 : Entails.eval a c18 := h 17 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c109 := h 108 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c448 := derived448 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨54, by decide⟩, true), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c671, some c510, some c780, some c79, some c81, some c72, some c82, some c63, some c265, some c104, some c256, some c475, some c3, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 57) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c763, c671, c510, c780, c79, c81, c72, c82, c63, c265, c104, c256, c475, c3] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c510 := derived510 a h
  have h3 : Entails.eval a c780 := derived780 a h
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c256 := h 255 (by decide)
  have h12 : Entails.eval a c475 := derived475 a h
  have h13 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, false), (⟨54, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c265, some c271, some c50, some c60, some c79, some c3, some c72, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 57) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c763, c265, c271, c50, c60, c79, c3, c72] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c265 := h 264 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c671, some c50, some c256, some c5, some c270, some c60, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 57) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c763, c671, c50, c256, c5, c270, c60] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c777, some c280, some c288, some c363, some c285, some c781, some c671, some c599, some c366, some c136, some c782, some c121, some c783, some c267, some c55, some c261, some c3, some c270, some c60, some c88, some c89, some c324, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c763, c777, c280, c288, c363, c285, c781, c671, c599, c366, c136, c782, c121, c783, c267, c55, c261, c3, c270, c60, c88, c89, c324] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c777 := derived777 a h
  have h2 : Entails.eval a c280 := h 279 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c363 := derived363 a h
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c781 := derived781 a h
  have h7 : Entails.eval a c671 := derived671 a h
  have h8 : Entails.eval a c599 := derived599 a h
  have h9 : Entails.eval a c366 := derived366 a h
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c782 := derived782 a h
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c783 := derived783 a h
  have h14 : Entails.eval a c267 := h 266 (by decide)
  have h15 : Entails.eval a c55 := h 54 (by decide)
  have h16 : Entails.eval a c261 := h 260 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c60 := h 59 (by decide)
  have h20 : Entails.eval a c88 := h 87 (by decide)
  have h21 : Entails.eval a c89 := h 88 (by decide)
  have h22 : Entails.eval a c324 := derived324 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c777, some c280, some c288, some c363, some c671, some c285, some c781, some c784, some c104, some c123, some c265, some c267, some c261, some c270, some c60, some c359, some c114, some c328, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c763, c777, c280, c288, c363, c671, c285, c781, c784, c104, c123, c265, c267, c261, c270, c60, c359, c114, c328] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c777 := derived777 a h
  have h2 : Entails.eval a c280 := h 279 (by decide)
  have h3 : Entails.eval a c288 := h 287 (by decide)
  have h4 : Entails.eval a c363 := derived363 a h
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c285 := h 284 (by decide)
  have h7 : Entails.eval a c781 := derived781 a h
  have h8 : Entails.eval a c784 := derived784 a h
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c123 := h 122 (by decide)
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c261 := h 260 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c359 := derived359 a h
  have h17 : Entails.eval a c114 := h 113 (by decide)
  have h18 : Entails.eval a c328 := derived328 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨49, by decide⟩, true), (⟨9, by decide⟩, true), (⟨51, by decide⟩, true), (⟨52, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c785, some c777, some c104, some c266, some c111, some c57, some c363, some c123, some c285, some c359, some c781, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c785, c777, c104, c266, c111, c57, c363, c123, c285, c359, c781] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c785 := derived785 a h
  have h1 : Entails.eval a c777 := derived777 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c363 := derived363 a h
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c359 := derived359 a h
  have h10 : Entails.eval a c781 := derived781 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨3, by decide⟩, true), (⟨42, by decide⟩, false), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨56, by decide⟩, true), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c72, some c273, some c451, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c263, c72, c273, c451] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c273 := h 272 (by decide)
  have h3 : Entails.eval a c451 := derived451 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false), (⟨42, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨47, by decide⟩, true), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c763, some c270, some c452, some c64, some c17, some c118, some c119, some c141, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c763, c270, c452, c64, c17, c118, c119, c141] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c763 := derived763 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c452 := derived452 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived788

end CochromaticTwenty.Certificates.B16_8_1
