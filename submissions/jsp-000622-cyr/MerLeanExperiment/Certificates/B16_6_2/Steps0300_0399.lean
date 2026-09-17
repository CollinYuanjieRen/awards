import MerLeanExperiment.Certificates.B16_6_2.Steps0200_0299

/-! Generated from the actual pinned b16_6_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_6_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c693 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c690, some c504, some c647, some c146, some c594, some c556, some c387, some c388, some c392, some c198, some c688, some c106, some c692, some c691, some c348, some c356, some c165, some c122, some c208, some c201, some c257, some c134, some c130, some c18, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c690, c504, c647, c146, c594, c556, c387, c388, c392, c198, c688, c106, c692, c691, c348, c356, c165, c122, c208, c201, c257, c134, c130, c18] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c647 := derived647 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c594 := derived594 a h
  have h5 : Entails.eval a c556 := derived556 a h
  have h6 : Entails.eval a c387 := h 386 (by decide)
  have h7 : Entails.eval a c388 := h 387 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c688 := derived688 a h
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c692 := derived692 a h
  have h13 : Entails.eval a c691 := derived691 a h
  have h14 : Entails.eval a c348 := h 347 (by decide)
  have h15 : Entails.eval a c356 := h 355 (by decide)
  have h16 : Entails.eval a c165 := h 164 (by decide)
  have h17 : Entails.eval a c122 := h 121 (by decide)
  have h18 : Entails.eval a c208 := h 207 (by decide)
  have h19 : Entails.eval a c201 := h 200 (by decide)
  have h20 : Entails.eval a c257 := h 256 (by decide)
  have h21 : Entails.eval a c134 := h 133 (by decide)
  have h22 : Entails.eval a c130 := h 129 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨52, by decide⟩, true), (⟨46, by decide⟩, false), (⟨11, by decide⟩, false), (⟨51, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c141, some c191, some c649, some c294, some c181, some c367, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c141, c191, c649, c294, c181, c367] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c649 := derived649 a h
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, false), (⟨39, by decide⟩, true), (⟨34, by decide⟩, true), (⟨40, by decide⟩, false), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c652, some c203, some c120, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c652, c203, c120] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c652 := derived652 a h
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨47, by decide⟩, true), (⟨42, by decide⟩, false), (⟨9, by decide⟩, true), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, false), (⟨51, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c694, some c352, some c336, some c381, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c694, c352, c336, c381] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c694 := derived694 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c504, some c647, some c693, some c194, some c690, some c146, some c594, some c556, some c387, some c348, some c356, some c165, some c122, some c208, some c260, some c198, some c164, some c695, some c141, some c161, some c649, some c358, some c558, some c183, some c696, some c340, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c504, c647, c693, c194, c690, c146, c594, c556, c387, c348, c356, c165, c122, c208, c260, c198, c164, c695, c141, c161, c649, c358, c558, c183, c696, c340] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c504 := derived504 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c693 := derived693 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c690 := derived690 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c594 := derived594 a h
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  have h16 : Entails.eval a c164 := h 163 (by decide)
  have h17 : Entails.eval a c695 := derived695 a h
  have h18 : Entails.eval a c141 := h 140 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c649 := derived649 a h
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c558 := derived558 a h
  have h23 : Entails.eval a c183 := h 182 (by decide)
  have h24 : Entails.eval a c696 := derived696 a h
  have h25 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c183, some c198, some c164, some c340, some c354, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c208, c183, c198, c164, c340, c354] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c340 := h 339 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨9, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c504, some c647, some c146, some c387, some c141, some c322, some c693, some c370, some c194, some c690, some c556, some c122, some c161, some c260, some c278, some c126, some c273, some c217, some c325, some c698, some c165, some c153, some c279, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c504, c647, c146, c387, c141, c322, c693, c370, c194, c690, c556, c122, c161, c260, c278, c126, c273, c217, c325, c698, c165, c153, c279] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c504 := derived504 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c322 := h 321 (by decide)
  have h6 : Entails.eval a c693 := derived693 a h
  have h7 : Entails.eval a c370 := h 369 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c690 := derived690 a h
  have h10 : Entails.eval a c556 := derived556 a h
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c161 := h 160 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c278 := h 277 (by decide)
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c273 := h 272 (by decide)
  have h17 : Entails.eval a c217 := h 216 (by decide)
  have h18 : Entails.eval a c325 := h 324 (by decide)
  have h19 : Entails.eval a c698 := derived698 a h
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  have h22 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨38, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c170, some c338, some c182, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c170, c338, c182] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c170 := h 169 (by decide)
  have h1 : Entails.eval a c338 := h 337 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c374, some c182, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c198, c374, c182] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c374 := h 373 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨15, by decide⟩, true), (⟨34, by decide⟩, false), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c283, some c278, some c361, some c153, some c163, some c321, some c207, some c152, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c283, c278, c361, c153, c163, c321, c207, c152] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c283 := h 282 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c361 := h 360 (by decide)
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c321 := h 320 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨34, by decide⟩, false), (⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨46, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c172, some c700, some c354, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c702, c172, c700, c354] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c172 := h 171 (by decide)
  have h2 : Entails.eval a c700 := derived700 a h
  have h3 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨9, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c504, some c647, some c693, some c194, some c370, some c146, some c690, some c701, some c387, some c141, some c699, some c703, some c183, some c208, some c697, some c340, some c627, some c283, some c361, some c268, some c266, some c114, some c237, some c138, some c273, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c504, c647, c693, c194, c370, c146, c690, c701, c387, c141, c699, c703, c183, c208, c697, c340, c627, c283, c361, c268, c266, c114, c237, c138, c273] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c504 := derived504 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c693 := derived693 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c690 := derived690 a h
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c699 := derived699 a h
  have h11 : Entails.eval a c703 := derived703 a h
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c697 := derived697 a h
  have h15 : Entails.eval a c340 := h 339 (by decide)
  have h16 : Entails.eval a c627 := derived627 a h
  have h17 : Entails.eval a c283 := h 282 (by decide)
  have h18 : Entails.eval a c361 := h 360 (by decide)
  have h19 : Entails.eval a c268 := h 267 (by decide)
  have h20 : Entails.eval a c266 := h 265 (by decide)
  have h21 : Entails.eval a c114 := h 113 (by decide)
  have h22 : Entails.eval a c237 := h 236 (by decide)
  have h23 : Entails.eval a c138 := h 137 (by decide)
  have h24 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c504, some c647, some c693, some c194, some c370, some c701, some c697, some c690, some c146, some c556, some c387, some c141, some c699, some c703, some c208, some c183, some c704, some c354, some c700, some c125, some c283, some c361, some c266, some c114, some c252, some c260, some c273, some c237, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c504, c647, c693, c194, c370, c701, c697, c690, c146, c556, c387, c141, c699, c703, c208, c183, c704, c354, c700, c125, c283, c361, c266, c114, c252, c260, c273, c237] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c504 := derived504 a h
  have h1 : Entails.eval a c647 := derived647 a h
  have h2 : Entails.eval a c693 := derived693 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c697 := derived697 a h
  have h7 : Entails.eval a c690 := derived690 a h
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c387 := h 386 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c699 := derived699 a h
  have h13 : Entails.eval a c703 := derived703 a h
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c183 := h 182 (by decide)
  have h16 : Entails.eval a c704 := derived704 a h
  have h17 : Entails.eval a c354 := h 353 (by decide)
  have h18 : Entails.eval a c700 := derived700 a h
  have h19 : Entails.eval a c125 := h 124 (by decide)
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c361 := h 360 (by decide)
  have h22 : Entails.eval a c266 := h 265 (by decide)
  have h23 : Entails.eval a c114 := h 113 (by decide)
  have h24 : Entails.eval a c252 := h 251 (by decide)
  have h25 : Entails.eval a c260 := h 259 (by decide)
  have h26 : Entails.eval a c273 := h 272 (by decide)
  have h27 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨37, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c647, some c504, some c693, some c194, some c370, some c700, some c705, some c701, some c697, some c690, some c146, some c556, some c283, some c361, some c114, some c260, some c128, some c239, some c237, some c203, some c266, some c273, some c140, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c647, c504, c693, c194, c370, c700, c705, c701, c697, c690, c146, c556, c283, c361, c114, c260, c128, c239, c237, c203, c266, c273, c140] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c647 := derived647 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c693 := derived693 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c700 := derived700 a h
  have h6 : Entails.eval a c705 := derived705 a h
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c697 := derived697 a h
  have h9 : Entails.eval a c690 := derived690 a h
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c556 := derived556 a h
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c361 := h 360 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c239 := h 238 (by decide)
  have h18 : Entails.eval a c237 := h 236 (by decide)
  have h19 : Entails.eval a c203 := h 202 (by decide)
  have h20 : Entails.eval a c266 := h 265 (by decide)
  have h21 : Entails.eval a c273 := h 272 (by decide)
  have h22 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c705, some c504, some c693, some c370, some c697, some c647, some c194, some c690, some c556, some c387, some c706, some c122, some c164, some c260, some c182, some c128, some c228, some c57, some c176, some c1, some c73, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c705, c504, c693, c370, c697, c647, c194, c690, c556, c387, c706, c122, c164, c260, c182, c128, c228, c57, c176, c1, c73] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c705 := derived705 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c693 := derived693 a h
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c697 := derived697 a h
  have h5 : Entails.eval a c647 := derived647 a h
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c690 := derived690 a h
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c387 := h 386 (by decide)
  have h10 : Entails.eval a c706 := derived706 a h
  have h11 : Entails.eval a c122 := h 121 (by decide)
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c182 := h 181 (by decide)
  have h15 : Entails.eval a c128 := h 127 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c176 := h 175 (by decide)
  have h19 : Entails.eval a c1 := h 0 (by decide)
  have h20 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c697, some c504, some c647, some c693, some c194, some c690, some c146, some c556, some c387, some c370, some c701, some c705, some c707, some c354, some c627, some c268, some c128, some c228, some c203, some c176, some c165, some c172, some c283, some c361, some c114, some c237, some c168, some c258, some c181, some c367, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c697, c504, c647, c693, c194, c690, c146, c556, c387, c370, c701, c705, c707, c354, c627, c268, c128, c228, c203, c176, c165, c172, c283, c361, c114, c237, c168, c258, c181, c367] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c697 := derived697 a h
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c647 := derived647 a h
  have h3 : Entails.eval a c693 := derived693 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c690 := derived690 a h
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c701 := derived701 a h
  have h11 : Entails.eval a c705 := derived705 a h
  have h12 : Entails.eval a c707 := derived707 a h
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c627 := derived627 a h
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c128 := h 127 (by decide)
  have h17 : Entails.eval a c228 := h 227 (by decide)
  have h18 : Entails.eval a c203 := h 202 (by decide)
  have h19 : Entails.eval a c176 := h 175 (by decide)
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c172 := h 171 (by decide)
  have h22 : Entails.eval a c283 := h 282 (by decide)
  have h23 : Entails.eval a c361 := h 360 (by decide)
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c237 := h 236 (by decide)
  have h26 : Entails.eval a c168 := h 167 (by decide)
  have h27 : Entails.eval a c258 := h 257 (by decide)
  have h28 : Entails.eval a c181 := h 180 (by decide)
  have h29 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c367, some c305, some c181, some c144, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c367, c305, c181, c144] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c367 := h 366 (by decide)
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨52, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c258, some c29, some c114, some c126, some c283, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c258, c29, c114, c126, c283] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c258 := h 257 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨52, by decide⟩, false), (⟨43, by decide⟩, false), (⟨8, by decide⟩, true), (⟨40, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, true), (⟨30, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c346, some c69, some c710, some c224, some c124, some c181, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c346, c69, c710, c224, c124, c181] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c346 := h 345 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c710 := derived710 a h
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c387, some c504, some c556, some c594, some c647, some c146, some c690, some c693, some c194, some c697, some c708, some c575, some c106, some c60, some c307, some c382, some c378, some c366, some c709, some c711, some c122, some c54, some c260, some c258, some c23, some c217, some c237, some c126, some c289, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c387, c504, c556, c594, c647, c146, c690, c693, c194, c697, c708, c575, c106, c60, c307, c382, c378, c366, c709, c711, c122, c54, c260, c258, c23, c217, c237, c126, c289] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c387 := h 386 (by decide)
  have h1 : Entails.eval a c504 := derived504 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c594 := derived594 a h
  have h4 : Entails.eval a c647 := derived647 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c690 := derived690 a h
  have h7 : Entails.eval a c693 := derived693 a h
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c697 := derived697 a h
  have h10 : Entails.eval a c708 := derived708 a h
  have h11 : Entails.eval a c575 := derived575 a h
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c382 := h 381 (by decide)
  have h16 : Entails.eval a c378 := h 377 (by decide)
  have h17 : Entails.eval a c366 := h 365 (by decide)
  have h18 : Entails.eval a c709 := derived709 a h
  have h19 : Entails.eval a c711 := derived711 a h
  have h20 : Entails.eval a c122 := h 121 (by decide)
  have h21 : Entails.eval a c54 := h 53 (by decide)
  have h22 : Entails.eval a c260 := h 259 (by decide)
  have h23 : Entails.eval a c258 := h 257 (by decide)
  have h24 : Entails.eval a c23 := h 22 (by decide)
  have h25 : Entails.eval a c217 := h 216 (by decide)
  have h26 : Entails.eval a c237 := h 236 (by decide)
  have h27 : Entails.eval a c126 := h 125 (by decide)
  have h28 : Entails.eval a c289 := h 288 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c146, some c200, some c709, some c183, some c388, some c79, some c3, some c11, some c105, some c107, some c141, some c98, some c35, some c322, some c51, some c327, some c302, some c49, some c91, some c109, some c382, some c84, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c73, c146, c200, c709, c183, c388, c79, c3, c11, c105, c107, c141, c98, c35, c322, c51, c327, c302, c49, c91, c109, c382, c84] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c709 := derived709 a h
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c322 := h 321 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  have h17 : Entails.eval a c302 := h 301 (by decide)
  have h18 : Entails.eval a c49 := h 48 (by decide)
  have h19 : Entails.eval a c91 := h 90 (by decide)
  have h20 : Entails.eval a c109 := h 108 (by decide)
  have h21 : Entails.eval a c382 := h 381 (by decide)
  have h22 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨14, by decide⟩, false), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c187, some c120, some c260, some c241, some c222, some c271, some c348, some c245, some c642, some c183, some c133, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c382, c187, c120, c260, c241, c222, c271, c348, c245, c642, c183, c133] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c241 := h 240 (by decide)
  have h5 : Entails.eval a c222 := h 221 (by decide)
  have h6 : Entails.eval a c271 := h 270 (by decide)
  have h7 : Entails.eval a c348 := h 347 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c642 := derived642 a h
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨48, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c60, some c348, some c222, some c54, some c260, some c258, some c541, some c217, some c305, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c106, c60, c348, c222, c54, c260, c258, c541, c217, c305] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c541 := derived541 a h
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨30, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c709, some c712, some c390, some c713, some c73, some c106, some c596, some c322, some c714, some c60, some c348, some c715, some c177, some c380, some c122, some c260, some c258, some c249, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c709, c712, c390, c713, c73, c106, c596, c322, c714, c60, c348, c715, c177, c380, c122, c260, c258, c249] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c709 := derived709 a h
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c713 := derived713 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c596 := derived596 a h
  have h7 : Entails.eval a c322 := h 321 (by decide)
  have h8 : Entails.eval a c714 := derived714 a h
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c715 := derived715 a h
  have h12 : Entails.eval a c177 := h 176 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, false), (⟨52, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c91, some c348, some c383, some c89, some c108, some c54, some c64, some c177, some c352, some c122, some c224, some c258, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c60, c91, c348, c383, c89, c108, c54, c64, c177, c352, c122, c224, c258] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c177 := h 176 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c224 := h 223 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c390, some c712, some c709, some c388, some c716, some c104, some c98, some c105, some c107, some c11, some c102, some c147, some c717, some c307, some c51, some c321, some c328, some c310, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c73, c390, c712, c709, c388, c716, c104, c98, c105, c107, c11, c102, c147, c717, c307, c51, c321, c328, c310] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c709 := derived709 a h
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c716 := derived716 a h
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c147 := h 146 (by decide)
  have h13 : Entails.eval a c717 := derived717 a h
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c321 := h 320 (by decide)
  have h17 : Entails.eval a c328 := h 327 (by decide)
  have h18 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c712, some c73, some c713, some c718, some c38, some c320, some c539, some c106, some c596, some c600, some c323, some c321, some c388, some c51, some c314, some c105, some c303, some c79, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c390, c712, c73, c713, c718, c38, c320, c539, c106, c596, c600, c323, c321, c388, c51, c314, c105, c303, c79] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c713 := derived713 a h
  have h4 : Entails.eval a c718 := derived718 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c539 := derived539 a h
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c596 := derived596 a h
  have h10 : Entails.eval a c600 := derived600 a h
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c321 := h 320 (by decide)
  have h13 : Entails.eval a c388 := h 387 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c314 := h 313 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨7, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c105, some c51, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c106, c105, c51] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c146, some c320, some c596, some c174, some c295, some c323, some c321, some c600, some c79, some c388, some c314, some c720, some c94, some c112, some c51, some c15, some c110, some c159, some c44, some c565, some c297, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c38, c146, c320, c596, c174, c295, c323, c321, c600, c79, c388, c314, c720, c94, c112, c51, c15, c110, c159, c44, c565, c297] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c596 := derived596 a h
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c321 := h 320 (by decide)
  have h8 : Entails.eval a c600 := derived600 a h
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c388 := h 387 (by decide)
  have h11 : Entails.eval a c314 := h 313 (by decide)
  have h12 : Entails.eval a c720 := derived720 a h
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c110 := h 109 (by decide)
  have h18 : Entails.eval a c159 := h 158 (by decide)
  have h19 : Entails.eval a c44 := h 43 (by decide)
  have h20 : Entails.eval a c565 := derived565 a h
  have h21 : Entails.eval a c297 := h 296 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c721, some c575, some c294, some c141, some c174, some c200, some c183, some c3, some c79, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c721, c575, c294, c141, c174, c200, c183, c3, c79] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c721 := derived721 a h
  have h1 : Entails.eval a c575 := derived575 a h
  have h2 : Entails.eval a c294 := h 293 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c174 := h 173 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c712, some c719, some c722, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c390, c712, c719, c722] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c719 := derived719 a h
  have h3 : Entails.eval a c722 := derived722 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c712, some c104, some c79, some c106, some c384, some c183, some c60, some c91, some c200, some c344, some c174, some c121, some c17, some c256, some c251, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c378, c712, c104, c79, c106, c384, c183, c60, c91, c200, c344, c174, c121, c17, c256, c251] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c384 := h 383 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c174 := h 173 (by decide)
  have h12 : Entails.eval a c121 := h 120 (by decide)
  have h13 : Entails.eval a c17 := h 16 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c390, some c723, some c724, some c107, some c378, some c105, some c91, some c383, some c384, some c372, some c60, some c348, some c344, some c294, some c174, some c113, some c161, some c19, some c206, some c177, some c245, some c582, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c712, c390, c723, c724, c107, c378, c105, c91, c383, c384, c372, c60, c348, c344, c294, c174, c113, c161, c19, c206, c177, c245, c582] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c724 := derived724 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c378 := h 377 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c383 := h 382 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c372 := h 371 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c348 := h 347 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c174 := h 173 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c19 := h 18 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c177 := h 176 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c582 := derived582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨30, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c294, some c378, some c723, some c390, some c712, some c724, some c105, some c107, some c91, some c182, some c383, some c384, some c372, some c388, some c725, some c200, some c198, some c3, some c11, some c113, some c98, some c253, some c18, some c138, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c294, c378, c723, c390, c712, c724, c105, c107, c91, c182, c383, c384, c372, c388, c725, c200, c198, c3, c11, c113, c98, c253, c18, c138] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c294 := h 293 (by decide)
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c724 := derived724 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c91 := h 90 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c383 := h 382 (by decide)
  have h11 : Entails.eval a c384 := h 383 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c388 := h 387 (by decide)
  have h14 : Entails.eval a c725 := derived725 a h
  have h15 : Entails.eval a c200 := h 199 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c11 := h 10 (by decide)
  have h19 : Entails.eval a c113 := h 112 (by decide)
  have h20 : Entails.eval a c98 := h 97 (by decide)
  have h21 : Entails.eval a c253 := h 252 (by decide)
  have h22 : Entails.eval a c18 := h 17 (by decide)
  have h23 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c253, some c251, some c117, some c302, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c256, c253, c251, c117, c302] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨47, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c383, some c302, some c372, some c582, some c159, some c209, some c326, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c712, c383, c302, c372, c582, c159, c209, c326] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c302 := h 301 (by decide)
  have h3 : Entails.eval a c372 := h 371 (by decide)
  have h4 : Entails.eval a c582 := derived582 a h
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c209 := h 208 (by decide)
  have h7 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨17, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨48, by decide⟩, true), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c390, some c200, some c113, some c203, some c208, some c159, some c326, some c152, some c209, some c204, some c260, some c228, some c137, some c291, some c273, some c126, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c712, c390, c200, c113, c203, c208, c159, c326, c152, c209, c204, c260, c228, c137, c291, c273, c126] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  have h7 : Entails.eval a c326 := h 325 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨47, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c390, some c712, some c200, some c208, some c11, some c198, some c42, some c727, some c113, some c203, some c728, some c729, some c328, some c327, some c316, some c211, some c258, some c607, some c264, some c132, some c177, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c723, c390, c712, c200, c208, c11, c198, c42, c727, c113, c203, c728, c729, c328, c327, c316, c211, c258, c607, c264, c132, c177] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c727 := derived727 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c728 := derived728 a h
  have h12 : Entails.eval a c729 := derived729 a h
  have h13 : Entails.eval a c328 := h 327 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c316 := h 315 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c607 := derived607 a h
  have h19 : Entails.eval a c264 := h 263 (by decide)
  have h20 : Entails.eval a c132 := h 131 (by decide)
  have h21 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨49, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c174, some c113, some c256, some c228, some c344, some c348, some c161, some c61, some c205, some c5, some c151, some c163, some c42, some c62, some c285, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c378, c174, c113, c256, c228, c344, c348, c161, c61, c205, c5, c151, c163, c42, c62, c285] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c174 := h 173 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c256 := h 255 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c205 := h 204 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c151 := h 150 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c723, some c390, some c712, some c294, some c726, some c731, some c200, some c183, some c79, some c730, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c378, c723, c390, c712, c294, c726, c731, c200, c183, c79, c730] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c712 := derived712 a h
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c726 := derived726 a h
  have h6 : Entails.eval a c731 := derived731 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c183 := h 182 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c730 := derived730 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c732, some c146, some c174, some c712, some c320, some c38, some c378, some c723, some c731, some c113, some c724, some c106, some c19, some c256, some c60, some c627, some c344, some c348, some c292, some c161, some c120, some c206, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c390, c732, c146, c174, c712, c320, c38, c378, c723, c731, c113, c724, c106, c19, c256, c60, c627, c344, c348, c292, c161, c120, c206] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c732 := derived732 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c378 := h 377 (by decide)
  have h8 : Entails.eval a c723 := derived723 a h
  have h9 : Entails.eval a c731 := derived731 a h
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c724 := derived724 a h
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c627 := derived627 a h
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c120 := h 119 (by decide)
  have h22 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c256, some c253, some c219, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c256, c253, c219] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c390, some c712, some c378, some c732, some c146, some c320, some c174, some c733, some c323, some c321, some c295, some c318, some c79, some c734, some c121, some c279, some c344, some c627, some c60, some c228, some c32, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c723, c390, c712, c378, c732, c146, c320, c174, c733, c323, c321, c295, c318, c79, c734, c121, c279, c344, c627, c60, c228, c32] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c732 := derived732 a h
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  have h7 : Entails.eval a c174 := h 173 (by decide)
  have h8 : Entails.eval a c733 := derived733 a h
  have h9 : Entails.eval a c323 := h 322 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c734 := derived734 a h
  have h15 : Entails.eval a c121 := h 120 (by decide)
  have h16 : Entails.eval a c279 := h 278 (by decide)
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c627 := derived627 a h
  have h19 : Entails.eval a c60 := h 59 (by decide)
  have h20 : Entails.eval a c228 := h 227 (by decide)
  have h21 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c241, some c177, some c382, some c380, some c122, some c114, some c129, some c337, some c299, some c539, some c346, some c282, some c38, some c146, some c83, some c144, some c13, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c241, c177, c382, c380, c122, c114, c129, c337, c299, c539, c346, c282, c38, c146, c83, c144, c13] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c177 := h 176 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c380 := h 379 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c337 := h 336 (by decide)
  have h8 : Entails.eval a c299 := h 298 (by decide)
  have h9 : Entails.eval a c539 := derived539 a h
  have h10 : Entails.eval a c346 := h 345 (by decide)
  have h11 : Entails.eval a c282 := h 281 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c723, some c390, some c712, some c221, some c344, some c736, some c260, some c228, some c128, some c187, some c146, some c200, some c278, some c208, some c198, some c170, some c341, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c735, c723, c390, c712, c221, c344, c736, c260, c228, c128, c187, c146, c200, c278, c208, c198, c170, c341] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c712 := derived712 a h
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c736 := derived736 a h
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c278 := h 277 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨32, by decide⟩, true), (⟨17, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c256, some c120, some c735, some c390, some c712, some c382, some c187, some c200, some c208, some c183, some c198, some c79, some c734, some c253, some c16, some c11, some c125, some c47, some c341, some c286, some c329, some c67, some c348, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c723, c256, c120, c735, c390, c712, c382, c187, c200, c208, c183, c198, c79, c734, c253, c16, c11, c125, c47, c341, c286, c329, c67, c348] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c735 := derived735 a h
  have h4 : Entails.eval a c390 := h 389 (by decide)
  have h5 : Entails.eval a c712 := derived712 a h
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c253 := h 252 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c125 := h 124 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c341 := h 340 (by decide)
  have h20 : Entails.eval a c286 := h 285 (by decide)
  have h21 : Entails.eval a c329 := h 328 (by decide)
  have h22 : Entails.eval a c67 := h 66 (by decide)
  have h23 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨17, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c256, some c735, some c390, some c712, some c120, some c738, some c228, some c344, some c348, some c329, some c177, some c161, some c202, some c203, some c200, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c723, c256, c735, c390, c712, c120, c738, c228, c344, c348, c329, c177, c161, c202, c203, c200] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c735 := derived735 a h
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c738 := derived738 a h
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c329 := h 328 (by decide)
  have h11 : Entails.eval a c177 := h 176 (by decide)
  have h12 : Entails.eval a c161 := h 160 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c712, some c737, some c739, some c322, some c323, some c320, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c390, c712, c737, c739, c322, c323, c320] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c323 := h 322 (by decide)
  have h6 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨30, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c344, some c348, some c53, some c329, some c539, some c177, some c161, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c390, c344, c348, c53, c329, c539, c177, c161] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c329 := h 328 (by decide)
  have h5 : Entails.eval a c539 := derived539 a h
  have h6 : Entails.eval a c177 := h 176 (by decide)
  have h7 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨24, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c723, some c390, some c146, some c741, some c228, some c128, some c187, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c735, c723, c390, c146, c741, c228, c128, c187] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c741 := derived741 a h
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c128 := h 127 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c735, some c723, some c390, some c712, some c256, some c739, some c742, some c307, some c228, some c344, some c348, some c291, some c53, some c329, some c177, some c380, some c122, some c161, some c249, some c331, some c273, some c272, some c126, some c234, some c2, some c363, some c104, some c70, some c105, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c735, c723, c390, c712, c256, c739, c742, c307, c228, c344, c348, c291, c53, c329, c177, c380, c122, c161, c249, c331, c273, c272, c126, c234, c2, c363, c104, c70, c105] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c735 := derived735 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c712 := derived712 a h
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c742 := derived742 a h
  have h7 : Entails.eval a c307 := h 306 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c291 := h 290 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c177 := h 176 (by decide)
  have h15 : Entails.eval a c380 := h 379 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c161 := h 160 (by decide)
  have h18 : Entails.eval a c249 := h 248 (by decide)
  have h19 : Entails.eval a c331 := h 330 (by decide)
  have h20 : Entails.eval a c273 := h 272 (by decide)
  have h21 : Entails.eval a c272 := h 271 (by decide)
  have h22 : Entails.eval a c126 := h 125 (by decide)
  have h23 : Entails.eval a c234 := h 233 (by decide)
  have h24 : Entails.eval a c2 := h 1 (by decide)
  have h25 : Entails.eval a c363 := h 362 (by decide)
  have h26 : Entails.eval a c104 := h 103 (by decide)
  have h27 : Entails.eval a c70 := h 69 (by decide)
  have h28 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c712, some c723, some c735, some c740, some c743, some c221, some c113, some c344, some c736, some c260, some c128, some c202, some c203, some c200, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c390, c712, c723, c735, c740, c743, c221, c113, c344, c736, c260, c128, c202, c203, c200] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c723 := derived723 a h
  have h3 : Entails.eval a c735 := derived735 a h
  have h4 : Entails.eval a c740 := derived740 a h
  have h5 : Entails.eval a c743 := derived743 a h
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c113 := h 112 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c736 := derived736 a h
  have h10 : Entails.eval a c260 := h 259 (by decide)
  have h11 : Entails.eval a c128 := h 127 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c228, some c128, some c187, some c200, some c208, some c188, some c198, some c79, some c16, some c11, some c75, some c55, some c82, some c350, some c105, some c71, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c228, c128, c187, c200, c208, c188, c198, c79, c16, c11, c75, c55, c82, c350, c105, c71] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c228 := h 227 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c350 := h 349 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c744, some c390, some c712, some c745, some c256, some c260, some c242, some c241, some c382, some c381, some c335, some c569, some c243, some c337, some c275, some c363, some c232, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c744, c390, c712, c745, c256, c260, c242, c241, c382, c381, c335, c569, c243, c337, c275, c363, c232] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c744 := derived744 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c745 := derived745 a h
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  have h10 : Entails.eval a c335 := h 334 (by decide)
  have h11 : Entails.eval a c569 := derived569 a h
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c337 := h 336 (by decide)
  have h14 : Entails.eval a c275 := h 274 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨49, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c744, some c746, some c344, some c348, some c221, some c330, some c329, some c256, some c382, some c381, some c247, some c249, some c331, some c272, some c275, some c363, some c232, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c744, c746, c344, c348, c221, c330, c329, c256, c382, c381, c247, c249, c331, c272, c275, c363, c232] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c744 := derived744 a h
  have h1 : Entails.eval a c746 := derived746 a h
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c348 := h 347 (by decide)
  have h4 : Entails.eval a c221 := h 220 (by decide)
  have h5 : Entails.eval a c330 := h 329 (by decide)
  have h6 : Entails.eval a c329 := h 328 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c331 := h 330 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c275 := h 274 (by decide)
  have h15 : Entails.eval a c363 := h 362 (by decide)
  have h16 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨37, by decide⟩, true), (⟨19, by decide⟩, false), (⟨24, by decide⟩, true), (⟨34, by decide⟩, true), (⟨48, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c222, some c232, some c381, some c275, some c249, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c222, c232, c381, c275, c249] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c222 := h 221 (by decide)
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  have h3 : Entails.eval a c275 := h 274 (by decide)
  have h4 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨34, by decide⟩, true), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c247, some c257, some c272, some c75, some c249, some c21, some c381, some c54, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c247, c257, c272, c75, c249, c21, c381, c54] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c247 := h 246 (by decide)
  have h1 : Entails.eval a c257 := h 256 (by decide)
  have h2 : Entails.eval a c272 := h 271 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨34, by decide⟩, true), (⟨41, by decide⟩, false), (⟨43, by decide⟩, true), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c247, some c749, some c222, some c122, some c381, some c179, some c249, some c200, some c275, some c208, some c251, some c139, some c377, some c79, some c16, some c11, some c87, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c378, c247, c749, c222, c122, c381, c179, c249, c200, c275, c208, c251, c139, c377, c79, c16, c11, c87] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c749 := derived749 a h
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c179 := h 178 (by decide)
  have h7 : Entails.eval a c249 := h 248 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c139 := h 138 (by decide)
  have h13 : Entails.eval a c377 := h 376 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c16 := h 15 (by decide)
  have h16 : Entails.eval a c11 := h 10 (by decide)
  have h17 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨41, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c744, some c390, some c712, some c750, some c260, some c222, some c122, some c179, some c146, some c200, some c294, some c299, some c209, some c256, some c575, some c141, some c175, some c3, some c79, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c744, c390, c712, c750, c260, c222, c122, c179, c146, c200, c294, c299, c209, c256, c575, c141, c175, c3, c79] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c744 := derived744 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c750 := derived750 a h
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c222 := h 221 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c256 := h 255 (by decide)
  have h14 : Entails.eval a c575 := derived575 a h
  have h15 : Entails.eval a c141 := h 140 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨41, by decide⟩, false), (⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c146, some c200, some c294, some c11, some c104, some c79, some c106, some c175, some c33, some c113, some c256, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c712, c146, c200, c294, c11, c104, c79, c106, c175, c33, c113, c256] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c294 := h 293 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c744, some c390, some c378, some c751, some c348, some c569, some c335, some c228, some c60, some c345, some c360, some c260, some c75, some c752, some c174, some c185, some c169, some c206, some c15, some c114, some c38, some c325, some c294, some c151, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c744, c390, c378, c751, c348, c569, c335, c228, c60, c345, c360, c260, c75, c752, c174, c185, c169, c206, c15, c114, c38, c325, c294, c151] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c744 := derived744 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c751 := derived751 a h
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c569 := derived569 a h
  have h6 : Entails.eval a c335 := h 334 (by decide)
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c360 := h 359 (by decide)
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c752 := derived752 a h
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c185 := h 184 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c206 := h 205 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c114 := h 113 (by decide)
  have h20 : Entails.eval a c38 := h 37 (by decide)
  have h21 : Entails.eval a c325 := h 324 (by decide)
  have h22 : Entails.eval a c294 := h 293 (by decide)
  have h23 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨44, by decide⟩, false), (⟨52, by decide⟩, true), (⟨1, by decide⟩, false), (⟨49, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c144, some c539, some c305, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c191, c144, c539, c305] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c539 := derived539 a h
  have h3 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨12, by decide⟩, false), (⟨42, by decide⟩, true), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c388, some c222, some c345, some c55, some c9, some c114, some c36, some c325, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c204, c388, c222, c345, c55, c9, c114, c36, c325] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c712, some c744, some c753, some c747, some c73, some c366, some c388, some c367, some c381, some c754, some c185, some c146, some c755, some c200, some c305, some c580, some c260, some c257, some c316, some c322, some c745, some c215, some c223, some c247, some c120, some c348, some c287, some c188, some c333, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c390, c712, c744, c753, c747, c73, c366, c388, c367, c381, c754, c185, c146, c755, c200, c305, c580, c260, c257, c316, c322, c745, c215, c223, c247, c120, c348, c287, c188, c333] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c744 := derived744 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c747 := derived747 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c388 := h 387 (by decide)
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  have h10 : Entails.eval a c754 := derived754 a h
  have h11 : Entails.eval a c185 := h 184 (by decide)
  have h12 : Entails.eval a c146 := h 145 (by decide)
  have h13 : Entails.eval a c755 := derived755 a h
  have h14 : Entails.eval a c200 := h 199 (by decide)
  have h15 : Entails.eval a c305 := h 304 (by decide)
  have h16 : Entails.eval a c580 := derived580 a h
  have h17 : Entails.eval a c260 := h 259 (by decide)
  have h18 : Entails.eval a c257 := h 256 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c322 := h 321 (by decide)
  have h21 : Entails.eval a c745 := derived745 a h
  have h22 : Entails.eval a c215 := h 214 (by decide)
  have h23 : Entails.eval a c223 := h 222 (by decide)
  have h24 : Entails.eval a c247 := h 246 (by decide)
  have h25 : Entails.eval a c120 := h 119 (by decide)
  have h26 : Entails.eval a c348 := h 347 (by decide)
  have h27 : Entails.eval a c287 := h 286 (by decide)
  have h28 : Entails.eval a c188 := h 187 (by decide)
  have h29 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨28, by decide⟩, true), (⟨42, by decide⟩, true), (⟨51, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c217, some c219, some c275, some c134, some c123, some c273, some c345, some c222, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c217, c219, c275, c134, c123, c273, c345, c222] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c217 := h 216 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨44, by decide⟩, false), (⟨14, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c390, some c756, some c194, some c388, some c146, some c305, some c316, some c381, some c200, some c73, some c580, some c322, some c321, some c757, some c260, some c222, some c241, some c348, some c345, some c271, some c20, some c167, some c245, some c188, some c60, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c712, c390, c756, c194, c388, c146, c305, c316, c381, c200, c73, c580, c322, c321, c757, c260, c222, c241, c348, c345, c271, c20, c167, c245, c188, c60] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c381 := h 380 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c580 := derived580 a h
  have h12 : Entails.eval a c322 := h 321 (by decide)
  have h13 : Entails.eval a c321 := h 320 (by decide)
  have h14 : Entails.eval a c757 := derived757 a h
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c222 := h 221 (by decide)
  have h17 : Entails.eval a c241 := h 240 (by decide)
  have h18 : Entails.eval a c348 := h 347 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c271 := h 270 (by decide)
  have h21 : Entails.eval a c20 := h 19 (by decide)
  have h22 : Entails.eval a c167 := h 166 (by decide)
  have h23 : Entails.eval a c245 := h 244 (by decide)
  have h24 : Entails.eval a c188 := h 187 (by decide)
  have h25 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨49, by decide⟩, false), (⟨42, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c256, some c241, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c260, c256, c241] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨24, by decide⟩, true), (⟨28, by decide⟩, true), (⟨42, by decide⟩, true), (⟨14, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c756, some c194, some c388, some c36, some c712, some c316, some c200, some c146, some c348, some c345, some c228, some c128, some c123, some c307, some c188, some c217, some c757, some c79, some c25, some c328, some c16, some c47, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c390, c756, c194, c388, c36, c712, c316, c200, c146, c348, c345, c228, c128, c123, c307, c188, c217, c757, c79, c25, c328, c16, c47] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c712 := derived712 a h
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c348 := h 347 (by decide)
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c128 := h 127 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c217 := h 216 (by decide)
  have h17 : Entails.eval a c757 := derived757 a h
  have h18 : Entails.eval a c79 := h 78 (by decide)
  have h19 : Entails.eval a c25 := h 24 (by decide)
  have h20 : Entails.eval a c328 := h 327 (by decide)
  have h21 : Entails.eval a c16 := h 15 (by decide)
  have h22 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨14, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c756, some c194, some c388, some c146, some c381, some c305, some c36, some c758, some c759, some c760, some c329, some c54, some c222, some c344, some c22, some c228, some c217, some c307, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c390, c756, c194, c388, c146, c381, c305, c36, c758, c759, c760, c329, c54, c222, c344, c22, c228, c217, c307] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c758 := derived758 a h
  have h9 : Entails.eval a c759 := derived759 a h
  have h10 : Entails.eval a c760 := derived760 a h
  have h11 : Entails.eval a c329 := h 328 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c217 := h 216 (by decide)
  have h18 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨24, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨51, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c257, some c135, some c134, some c188, some c273, some c249, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c257, c135, c134, c188, c273, c249] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c257 := h 256 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨17, by decide⟩, false), (⟨34, by decide⟩, true), (⟨20, by decide⟩, false), (⟨48, by decide⟩, true), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨14, by decide⟩, true), (⟨11, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c748, some c232, some c134, some c253, some c28, some c29, some c102, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c748, c232, c134, c253, c28, c29, c102] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c748 := derived748 a h
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c253 := h 252 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c756, some c712, some c390, some c200, some c194, some c761, some c388, some c372, some c762, some c76, some c367, some c228, some c249, some c348, some c344, some c221, some c331, some c763, some c363, some c123, some c330, some c275, some c384, some c251, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c756, c712, c390, c200, c194, c761, c388, c372, c762, c76, c367, c228, c249, c348, c344, c221, c331, c763, c363, c123, c330, c275, c384, c251] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c756 := derived756 a h
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c390 := h 389 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c762 := derived762 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c348 := h 347 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c221 := h 220 (by decide)
  have h16 : Entails.eval a c331 := h 330 (by decide)
  have h17 : Entails.eval a c763 := derived763 a h
  have h18 : Entails.eval a c363 := h 362 (by decide)
  have h19 : Entails.eval a c123 := h 122 (by decide)
  have h20 : Entails.eval a c330 := h 329 (by decide)
  have h21 : Entails.eval a c275 := h 274 (by decide)
  have h22 : Entails.eval a c384 := h 383 (by decide)
  have h23 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨14, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c390, some c756, some c194, some c388, some c761, some c372, some c200, some c146, some c764, some c307, some c188, some c120, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c712, c390, c756, c194, c388, c761, c372, c200, c146, c764, c307, c188, c120] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c372 := h 371 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c764 := derived764 a h
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c756, some c390, some c712, some c146, some c200, some c194, some c388, some c761, some c367, some c372, some c765, some c260, some c256, some c759, some c221, some c382, some c299, some c344, some c209, some c337, some c278, some c166, some c363, some c339, some c170, some c186, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c756, c390, c712, c146, c200, c194, c388, c761, c367, c372, c765, c260, c256, c759, c221, c382, c299, c344, c209, c337, c278, c166, c363, c339, c170, c186] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c756 := derived756 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c388 := h 387 (by decide)
  have h7 : Entails.eval a c761 := derived761 a h
  have h8 : Entails.eval a c367 := h 366 (by decide)
  have h9 : Entails.eval a c372 := h 371 (by decide)
  have h10 : Entails.eval a c765 := derived765 a h
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c759 := derived759 a h
  have h14 : Entails.eval a c221 := h 220 (by decide)
  have h15 : Entails.eval a c382 := h 381 (by decide)
  have h16 : Entails.eval a c299 := h 298 (by decide)
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c337 := h 336 (by decide)
  have h20 : Entails.eval a c278 := h 277 (by decide)
  have h21 : Entails.eval a c166 := h 165 (by decide)
  have h22 : Entails.eval a c363 := h 362 (by decide)
  have h23 : Entails.eval a c339 := h 338 (by decide)
  have h24 : Entails.eval a c170 := h 169 (by decide)
  have h25 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨30, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c299, some c179, some c114, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c299, c179, c114] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c299 := h 298 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨48, by decide⟩, true), (⟨24, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c759, some c222, some c241, some c73, some c348, some c20, some c60, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c260, c759, c222, c241, c73, c348, c20, c60] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c759 := derived759 a h
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c241 := h 240 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨24, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c766, some c756, some c390, some c768, some c381, some c179, some c767, some c122, some c38, some c348, some c60, some c337, some c15, some c360, some c167, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c260, c766, c756, c390, c768, c381, c179, c767, c122, c38, c348, c60, c337, c15, c360, c167] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c768 := derived768 a h
  have h5 : Entails.eval a c381 := h 380 (by decide)
  have h6 : Entails.eval a c179 := h 178 (by decide)
  have h7 : Entails.eval a c767 := derived767 a h
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c337 := h 336 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c360 := h 359 (by decide)
  have h15 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c756, some c260, some c769, some c382, some c187, some c222, some c348, some c167, some c345, some c360, some c143, some c169, some c281, some c205, some c114, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c766, c756, c260, c769, c382, c187, c222, c348, c167, c345, c360, c143, c169, c281, c205, c114] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c769 := derived769 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c222 := h 221 (by decide)
  have h7 : Entails.eval a c348 := h 347 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c360 := h 359 (by decide)
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c114 := h 113 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c228, some c128, some c187, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c228, c128, c187] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c228 := h 227 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨34, by decide⟩, true), (⟨14, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c222, some c122, some c179, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c222, c122, c179] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c222 := h 221 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c770, some c771, some c348, some c772, some c756, some c382, some c381, some c179, some c249, some c258, some c272, some c367, some c135, some c344, some c202, some c161, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c766, c770, c771, c348, c772, c756, c382, c381, c179, c249, c258, c272, c367, c135, c344, c202, c161] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c770 := derived770 a h
  have h2 : Entails.eval a c771 := derived771 a h
  have h3 : Entails.eval a c348 := h 347 (by decide)
  have h4 : Entails.eval a c772 := derived772 a h
  have h5 : Entails.eval a c756 := derived756 a h
  have h6 : Entails.eval a c382 := h 381 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c249 := h 248 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c367 := h 366 (by decide)
  have h13 : Entails.eval a c135 := h 134 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨49, by decide⟩, true), (⟨14, by decide⟩, false), (⟨41, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c73, some c367, some c754, some c185, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c73, c367, c754, c185] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c73 := h 72 (by decide)
  have h1 : Entails.eval a c367 := h 366 (by decide)
  have h2 : Entails.eval a c754 := derived754 a h
  have h3 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c756, some c390, some c766, some c770, some c771, some c348, some c772, some c773, some c329, some c344, some c73, some c774, some c388, some c190, some c202, some c539, some c581, some c582, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c756, c390, c766, c770, c771, c348, c772, c773, c329, c344, c73, c774, c388, c190, c202, c539, c581, c582] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c756 := derived756 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c770 := derived770 a h
  have h4 : Entails.eval a c771 := derived771 a h
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c772 := derived772 a h
  have h7 : Entails.eval a c773 := derived773 a h
  have h8 : Entails.eval a c329 := h 328 (by decide)
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c774 := derived774 a h
  have h12 : Entails.eval a c388 := h 387 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c539 := derived539 a h
  have h16 : Entails.eval a c581 := derived581 a h
  have h17 : Entails.eval a c582 := derived582 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨24, by decide⟩, true), (⟨14, by decide⟩, false), (⟨34, by decide⟩, true), (⟨41, by decide⟩, false), (⟨11, by decide⟩, true), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c378, some c772, some c749, some c174, some c249, some c258, some c272, some c76, some c372, some c135, some c115, some c22, some c206, some c303, some c54, some c320, some c297, some c294, some c149, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c378, c772, c749, c174, c249, c258, c272, c76, c372, c135, c115, c22, c206, c303, c54, c320, c297, c294, c149] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c378 := h 377 (by decide)
  have h1 : Entails.eval a c772 := derived772 a h
  have h2 : Entails.eval a c749 := derived749 a h
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c258 := h 257 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c372 := h 371 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c115 := h 114 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c303 := h 302 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c294 := h 293 (by decide)
  have h18 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c162, some c363, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c163, c162, c363] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c363 := h 362 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c348, some c775, some c378, some c756, some c390, some c712, some c174, some c772, some c260, some c749, some c776, some c381, some c185, some c383, some c332, some c777, some c344, some c190, some c191, some c388, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c348, c775, c378, c756, c390, c712, c174, c772, c260, c749, c776, c381, c185, c383, c332, c777, c344, c190, c191, c388] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c348 := h 347 (by decide)
  have h1 : Entails.eval a c775 := derived775 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c756 := derived756 a h
  have h4 : Entails.eval a c390 := h 389 (by decide)
  have h5 : Entails.eval a c712 := derived712 a h
  have h6 : Entails.eval a c174 := h 173 (by decide)
  have h7 : Entails.eval a c772 := derived772 a h
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c749 := derived749 a h
  have h10 : Entails.eval a c776 := derived776 a h
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c383 := h 382 (by decide)
  have h14 : Entails.eval a c332 := h 331 (by decide)
  have h15 : Entails.eval a c777 := derived777 a h
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  have h19 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c390, some c756, some c778, some c194, some c388, some c775, some c146, some c294, some c712, some c200, some c348, some c381, some c305, some c222, some c54, some c144, some c36, some c311, some c260, some c257, some c6, some c344, some c135, some c161, some c203, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c390, c756, c778, c194, c388, c775, c146, c294, c712, c200, c348, c381, c305, c222, c54, c144, c36, c311, c260, c257, c6, c344, c135, c161, c203] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c390 := h 389 (by decide)
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c778 := derived778 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c775 := derived775 a h
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  have h8 : Entails.eval a c712 := derived712 a h
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c311 := h 310 (by decide)
  have h18 : Entails.eval a c260 := h 259 (by decide)
  have h19 : Entails.eval a c257 := h 256 (by decide)
  have h20 : Entails.eval a c6 := h 5 (by decide)
  have h21 : Entails.eval a c344 := h 343 (by decide)
  have h22 : Entails.eval a c135 := h 134 (by decide)
  have h23 : Entails.eval a c161 := h 160 (by decide)
  have h24 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c775, some c378, some c756, some c390, some c712, some c348, some c778, some c146, some c200, some c194, some c294, some c388, some c779, some c76, some c372, some c377, some c175, some c150, some c141, some c113, some c344, some c256, some c162, some c762, some c249, some c251, some c763, some c28, some c253, some c286, some c37, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c775, c378, c756, c390, c712, c348, c778, c146, c200, c194, c294, c388, c779, c76, c372, c377, c175, c150, c141, c113, c344, c256, c162, c762, c249, c251, c763, c28, c253, c286, c37] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c775 := derived775 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c348 := h 347 (by decide)
  have h6 : Entails.eval a c778 := derived778 a h
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c388 := h 387 (by decide)
  have h12 : Entails.eval a c779 := derived779 a h
  have h13 : Entails.eval a c76 := h 75 (by decide)
  have h14 : Entails.eval a c372 := h 371 (by decide)
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c150 := h 149 (by decide)
  have h18 : Entails.eval a c141 := h 140 (by decide)
  have h19 : Entails.eval a c113 := h 112 (by decide)
  have h20 : Entails.eval a c344 := h 343 (by decide)
  have h21 : Entails.eval a c256 := h 255 (by decide)
  have h22 : Entails.eval a c162 := h 161 (by decide)
  have h23 : Entails.eval a c762 := derived762 a h
  have h24 : Entails.eval a c249 := h 248 (by decide)
  have h25 : Entails.eval a c251 := h 250 (by decide)
  have h26 : Entails.eval a c763 := derived763 a h
  have h27 : Entails.eval a c28 := h 27 (by decide)
  have h28 : Entails.eval a c253 := h 252 (by decide)
  have h29 : Entails.eval a c286 := h 285 (by decide)
  have h30 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c775, some c378, some c780, some c228, some c260, some c390, some c772, some c222, some c122, some c146, some c299, some c294, some c209, some c570, some c256, some c33, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 57) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c775, c378, c780, c228, c260, c390, c772, c222, c122, c146, c299, c294, c209, c570, c256, c33] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c775 := derived775 a h
  have h1 : Entails.eval a c378 := h 377 (by decide)
  have h2 : Entails.eval a c780 := derived780 a h
  have h3 : Entails.eval a c228 := h 227 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c390 := h 389 (by decide)
  have h6 : Entails.eval a c772 := derived772 a h
  have h7 : Entails.eval a c222 := h 221 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c294 := h 293 (by decide)
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c570 := derived570 a h
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c781, some c775, some c378, some c780, some c228, some c260, some c60, some c756, some c390, some c346, some c361, some c360, some c167, some c166, some c206, some c202, some c15, some c114, some c129, some c38, some c325, some c256, some c294, some c311, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 57) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c781, c775, c378, c780, c228, c260, c60, c756, c390, c346, c361, c360, c167, c166, c206, c202, c15, c114, c129, c38, c325, c256, c294, c311] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c781 := derived781 a h
  have h1 : Entails.eval a c775 := derived775 a h
  have h2 : Entails.eval a c378 := h 377 (by decide)
  have h3 : Entails.eval a c780 := derived780 a h
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c756 := derived756 a h
  have h8 : Entails.eval a c390 := h 389 (by decide)
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c360 := h 359 (by decide)
  have h12 : Entails.eval a c167 := h 166 (by decide)
  have h13 : Entails.eval a c166 := h 165 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c15 := h 14 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  have h18 : Entails.eval a c129 := h 128 (by decide)
  have h19 : Entails.eval a c38 := h 37 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  have h21 : Entails.eval a c256 := h 255 (by decide)
  have h22 : Entails.eval a c294 := h 293 (by decide)
  have h23 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c107, some c104, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 57) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c106, c107, c104] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c784 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, true), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨54, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f784 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c38, some c146, some c15, some c185, some c169, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p784 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked784 : lratChecker f784 p784 = .success := by decide +kernel
theorem unsat784 : Unsatisfiable (PosFin 57) f784 := by
  apply lratCheckerSound f784 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p784
  · intro a ha; simp [p784] at ha; subst a; trivial
  · exact checked784
theorem derived784 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c784 := by
  apply localUnsat_implies_entails f784 [c38, c146, c15, c185, c169] c784 unsat784 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c785 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f785 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c390, some c756, some c775, some c378, some c780, some c228, some c60, some c260, some c781, some c782, some c337, some c783, some c784, some c294, some c575, some c256, some c113, some c209, some c174, some c283, some c194, some c166, some c345, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p785 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked785 : lratChecker f785 p785 = .success := by decide +kernel
theorem unsat785 : Unsatisfiable (PosFin 57) f785 := by
  apply lratCheckerSound f785 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p785
  · intro a ha; simp [p785] at ha; subst a; trivial
  · exact checked785
theorem derived785 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c785 := by
  apply localUnsat_implies_entails f785 [c712, c390, c756, c775, c378, c780, c228, c60, c260, c781, c782, c337, c783, c784, c294, c575, c256, c113, c209, c174, c283, c194, c166, c345] c785 unsat785 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c390 := h 389 (by decide)
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c775 := derived775 a h
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c780 := derived780 a h
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c781 := derived781 a h
  have h10 : Entails.eval a c782 := derived782 a h
  have h11 : Entails.eval a c337 := h 336 (by decide)
  have h12 : Entails.eval a c783 := derived783 a h
  have h13 : Entails.eval a c784 := derived784 a h
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c575 := derived575 a h
  have h16 : Entails.eval a c256 := h 255 (by decide)
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c209 := h 208 (by decide)
  have h19 : Entails.eval a c174 := h 173 (by decide)
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c194 := h 193 (by decide)
  have h22 : Entails.eval a c166 := h 165 (by decide)
  have h23 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c786 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨15, by decide⟩, false), (⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨30, by decide⟩, false), (⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f786 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c369, some c24, some c241, some c294, some c175, some c113, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p786 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked786 : lratChecker f786 p786 = .success := by decide +kernel
theorem unsat786 : Unsatisfiable (PosFin 57) f786 := by
  apply lratCheckerSound f786 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p786
  · intro a ha; simp [p786] at ha; subst a; trivial
  · exact checked786
theorem derived786 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c786 := by
  apply localUnsat_implies_entails f786 [c74, c369, c24, c241, c294, c175, c113] c786 unsat786 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c241 := h 240 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c787 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨17, by decide⟩, true), (⟨48, by decide⟩, true), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f787 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c228, some c786, some c381, some c299, some c337, some c34, some c142, some c313, some c110, some c24, some c8, some c104, some c209, some c32, some c294, some c443, some c221, some c360, some c279, some c233, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p787 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked787 : lratChecker f787 p787 = .success := by decide +kernel
theorem unsat787 : Unsatisfiable (PosFin 57) f787 := by
  apply lratCheckerSound f787 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p787
  · intro a ha; simp [p787] at ha; subst a; trivial
  · exact checked787
theorem derived787 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c787 := by
  apply localUnsat_implies_entails f787 [c60, c228, c786, c381, c299, c337, c34, c142, c313, c110, c24, c8, c104, c209, c32, c294, c443, c221, c360, c279, c233] c787 unsat787 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c786 := derived786 a h
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c299 := h 298 (by decide)
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c142 := h 141 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c294 := h 293 (by decide)
  have h16 : Entails.eval a c443 := derived443 a h
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c360 := h 359 (by decide)
  have h19 : Entails.eval a c279 := h 278 (by decide)
  have h20 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c788 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f788 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c386, some c785, some c712, some c228, some c60, some c256, some c787, some c193, some c200, some c179, some c74, some c24, some c241, some c294, some c174, some c113, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p788 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked788 : lratChecker f788 p788 = .success := by decide +kernel
theorem unsat788 : Unsatisfiable (PosFin 57) f788 := by
  apply lratCheckerSound f788 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p788
  · intro a ha; simp [p788] at ha; subst a; trivial
  · exact checked788
theorem derived788 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c788 := by
  apply localUnsat_implies_entails f788 [c386, c785, c712, c228, c60, c256, c787, c193, c200, c179, c74, c24, c241, c294, c174, c113] c788 unsat788 (by rfl) a
  have h0 : Entails.eval a c386 := h 385 (by decide)
  have h1 : Entails.eval a c785 := derived785 a h
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c228 := h 227 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c787 := derived787 a h
  have h7 : Entails.eval a c193 := h 192 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c241 := h 240 (by decide)
  have h13 : Entails.eval a c294 := h 293 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c789 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨54, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f789 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c771, some c128, some c200, some c188, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p789 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked789 : lratChecker f789 p789 = .success := by decide +kernel
theorem unsat789 : Unsatisfiable (PosFin 57) f789 := by
  apply lratCheckerSound f789 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p789
  · intro a ha; simp [p789] at ha; subst a; trivial
  · exact checked789
theorem derived789 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c789 := by
  apply localUnsat_implies_entails f789 [c771, c128, c200, c188] c789 unsat789 (by rfl) a
  have h0 : Entails.eval a c771 := derived771 a h
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c790 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨22, by decide⟩, true), (⟨33, by decide⟩, false), (⟨17, by decide⟩, true), (⟨47, by decide⟩, false), (⟨48, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f790 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c126, some c188, some c278, some c113, some c201, some c198, some c171, some c341, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p790 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked790 : lratChecker f790 p790 = .success := by decide +kernel
theorem unsat790 : Unsatisfiable (PosFin 57) f790 := by
  apply lratCheckerSound f790 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p790
  · intro a ha; simp [p790] at ha; subst a; trivial
  · exact checked790
theorem derived790 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c790 := by
  apply localUnsat_implies_entails f790 [c200, c126, c188, c278, c113, c201, c198, c171, c341] c790 unsat790 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c278 := h 277 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c791 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨14, by decide⟩, false), (⟨33, by decide⟩, false), (⟨32, by decide⟩, true), (⟨42, by decide⟩, true), (⟨30, by decide⟩, false), (⟨49, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f791 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c159, some c171, some c341, some c368, some c192, some c306, some c205, some c313, some c157, some c325, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p791 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked791 : lratChecker f791 p791 = .success := by decide +kernel
theorem unsat791 : Unsatisfiable (PosFin 57) f791 := by
  apply lratCheckerSound f791 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p791
  · intro a ha; simp [p791] at ha; subst a; trivial
  · exact checked791
theorem derived791 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c791 := by
  apply localUnsat_implies_entails f791 [c369, c159, c171, c341, c368, c192, c306, c205, c313, c157, c325] c791 unsat791 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c341 := h 340 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c205 := h 204 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c792 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨14, by decide⟩, false), (⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨41, by decide⟩, true), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f792 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c201, some c130, some c272, some c131, some c243, some c185, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p792 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked792 : lratChecker f792 p792 = .success := by decide +kernel
theorem unsat792 : Unsatisfiable (PosFin 57) f792 := by
  apply lratCheckerSound f792 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p792
  · intro a ha; simp [p792] at ha; subst a; trivial
  · exact checked792
theorem derived792 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c792 := by
  apply localUnsat_implies_entails f792 [c208, c201, c130, c272, c131, c243, c185] c792 unsat792 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived792

end CochromaticTwenty.Certificates.B16_6_2
