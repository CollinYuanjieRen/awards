import MerLeanExperiment.Certificates.B16_2_2.Steps0200_0299

/-! Generated from the actual pinned b16_2_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_2_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c684 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨42, by decide⟩, true), (⟨48, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c229, some c370, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c233, c229, c370] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c229 := h 228 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨10, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨51, by decide⟩, true), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c681, some c3, some c112, some c189, some c190, some c183, some c669, some c668, some c683, some c682, some c108, some c24, some c31, some c173, some c107, some c361, some c37, some c91, some c371, some c684, some c262, some c248, some c240, some c356, some c370, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c681, c3, c112, c189, c190, c183, c669, c668, c683, c682, c108, c24, c31, c173, c107, c361, c37, c91, c371, c684, c262, c248, c240, c356, c370] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c681 := derived681 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c669 := derived669 a h
  have h7 : Entails.eval a c668 := derived668 a h
  have h8 : Entails.eval a c683 := derived683 a h
  have h9 : Entails.eval a c682 := derived682 a h
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c173 := h 172 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c361 := h 360 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c91 := h 90 (by decide)
  have h18 : Entails.eval a c371 := h 370 (by decide)
  have h19 : Entails.eval a c684 := derived684 a h
  have h20 : Entails.eval a c262 := h 261 (by decide)
  have h21 : Entails.eval a c248 := h 247 (by decide)
  have h22 : Entails.eval a c240 := h 239 (by decide)
  have h23 : Entails.eval a c356 := h 355 (by decide)
  have h24 : Entails.eval a c370 := h 369 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨24, by decide⟩, true), (⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨45, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c90, some c84, some c522, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c90, c84, c522] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c90 := h 89 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨45, by decide⟩, true), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c264, some c240, some c27, some c263, some c233, some c262, some c686, some c112, some c3, some c250, some c245, some c359, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c264, c240, c27, c263, c233, c262, c686, c112, c3, c250, c245, c359] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c264 := h 263 (by decide)
  have h1 : Entails.eval a c240 := h 239 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c686 := derived686 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨45, by decide⟩, true), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c15, some c86, some c250, some c365, some c377, some c381, some c547, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c3, c15, c86, c250, c365, c377, c381, c547] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c365 := h 364 (by decide)
  have h5 : Entails.eval a c377 := h 376 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c547 := derived547 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨56, by decide⟩, false), (⟨41, by decide⟩, false), (⟨44, by decide⟩, false), (⟨45, by decide⟩, true), (⟨15, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c264, some c164, some c370, some c369, some c27, some c687, some c371, some c688, some c112, some c667, some c77, some c166, some c250, some c361, some c381, some c520, some c181, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c263, c264, c164, c370, c369, c27, c687, c371, c688, c112, c667, c77, c166, c250, c361, c381, c520, c181] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c687 := derived687 a h
  have h7 : Entails.eval a c371 := h 370 (by decide)
  have h8 : Entails.eval a c688 := derived688 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c667 := derived667 a h
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c166 := h 165 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c381 := h 380 (by decide)
  have h16 : Entails.eval a c520 := derived520 a h
  have h17 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨49, by decide⟩, false), (⟨46, by decide⟩, true), (⟨51, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c362, some c361, some c377, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c362, c361, c377] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c362 := h 361 (by decide)
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c377 := h 376 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨46, by decide⟩, true), (⟨51, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c110, some c106, some c2, some c93, some c376, some c241, some c97, some c31, some c29, some c690, some c371, some c237, some c120, some c262, some c662, some c629, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c3, c110, c106, c2, c93, c376, c241, c97, c31, c29, c690, c371, c237, c120, c262, c662, c629] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c690 := derived690 a h
  have h11 : Entails.eval a c371 := h 370 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c262 := h 261 (by decide)
  have h15 : Entails.eval a c662 := derived662 a h
  have h16 : Entails.eval a c629 := derived629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨24, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c241, some c29, some c248, some c183, some c120, some c671, some c672, some c681, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c241, c29, c248, c183, c120, c671, c672, c681] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c183 := h 182 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c672 := derived672 a h
  have h7 : Entails.eval a c681 := derived681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨50, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨51, by decide⟩, true), (⟨53, by decide⟩, false), (⟨48, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c237, some c692, some c178, some c113, some c29, some c248, some c183, some c364, some c190, some c380, some c182, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c237, c692, c178, c113, c29, c248, c183, c364, c190, c380, c182] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c237 := h 236 (by decide)
  have h1 : Entails.eval a c692 := derived692 a h
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c364 := h 363 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨46, by decide⟩, true), (⟨8, by decide⟩, false), (⟨53, by decide⟩, false), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c106, some c250, some c263, some c264, some c122, some c691, some c693, some c371, some c362, some c361, some c381, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c110, c106, c250, c263, c264, c122, c691, c693, c371, c362, c361, c381] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c250 := h 249 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c264 := h 263 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c691 := derived691 a h
  have h7 : Entails.eval a c693 := derived693 a h
  have h8 : Entails.eval a c371 := h 370 (by decide)
  have h9 : Entails.eval a c362 := h 361 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c362, some c361, some c381, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c362, c361, c381] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c362 := h 361 (by decide)
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨18, by decide⟩, true), (⟨53, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c24, some c109, some c33, some c236, some c375, some c237, some c29, some c241, some c258, some c94, some c1, some c629, some c112, some c113, some c116, some c91, some c12, some c662, some c165, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c371, c24, c109, c33, c236, c375, c237, c29, c241, c258, c94, c1, c629, c112, c113, c116, c91, c12, c662, c165] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c237 := h 236 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c241 := h 240 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c629 := derived629 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c116 := h 115 (by decide)
  have h16 : Entails.eval a c91 := h 90 (by decide)
  have h17 : Entails.eval a c12 := h 11 (by decide)
  have h18 : Entails.eval a c662 := derived662 a h
  have h19 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c695, some c371, some c236, some c375, some c237, some c24, some c381, some c248, some c78, some c109, some c33, some c696, some c107, some c105, some c91, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c695, c371, c236, c375, c237, c24, c381, c248, c78, c109, c33, c696, c107, c105, c91] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c695 := derived695 a h
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c248 := h 247 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c696 := derived696 a h
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, true), (⟨24, by decide⟩, false), (⟨43, by decide⟩, false), (⟨51, by decide⟩, true), (⟨42, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c165, some c120, some c183, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c165, c120, c183] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c165 := h 164 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c695, some c371, some c237, some c24, some c264, some c236, some c697, some c80, some c364, some c380, some c78, some c109, some c106, some c694, some c696, some c262, some c629, some c698, some c12, some c9, some c111, some c3, some c94, some c171, some c376, some c13, some c188, some c72, some c70, some c190, some c159, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c263, c695, c371, c237, c24, c264, c236, c697, c80, c364, c380, c78, c109, c106, c694, c696, c262, c629, c698, c12, c9, c111, c3, c94, c171, c376, c13, c188, c72, c70, c190, c159] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c695 := derived695 a h
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c236 := h 235 (by decide)
  have h7 : Entails.eval a c697 := derived697 a h
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c364 := h 363 (by decide)
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c106 := h 105 (by decide)
  have h14 : Entails.eval a c694 := derived694 a h
  have h15 : Entails.eval a c696 := derived696 a h
  have h16 : Entails.eval a c262 := h 261 (by decide)
  have h17 : Entails.eval a c629 := derived629 a h
  have h18 : Entails.eval a c698 := derived698 a h
  have h19 : Entails.eval a c12 := h 11 (by decide)
  have h20 : Entails.eval a c9 := h 8 (by decide)
  have h21 : Entails.eval a c111 := h 110 (by decide)
  have h22 : Entails.eval a c3 := h 2 (by decide)
  have h23 : Entails.eval a c94 := h 93 (by decide)
  have h24 : Entails.eval a c171 := h 170 (by decide)
  have h25 : Entails.eval a c376 := h 375 (by decide)
  have h26 : Entails.eval a c13 := h 12 (by decide)
  have h27 : Entails.eval a c188 := h 187 (by decide)
  have h28 : Entails.eval a c72 := h 71 (by decide)
  have h29 : Entails.eval a c70 := h 69 (by decide)
  have h30 : Entails.eval a c190 := h 189 (by decide)
  have h31 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨50, by decide⟩, false), (⟨46, by decide⟩, true), (⟨42, by decide⟩, false), (⟨48, by decide⟩, true), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c264, some c695, some c371, some c236, some c375, some c699, some c366, some c365, some c381, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c263, c264, c695, c371, c236, c375, c699, c366, c365, c381] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c695 := derived695 a h
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c699 := derived699 a h
  have h7 : Entails.eval a c366 := h 365 (by decide)
  have h8 : Entails.eval a c365 := h 364 (by decide)
  have h9 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨55, by decide⟩, false), (⟨47, by decide⟩, true), (⟨44, by decide⟩, true), (⟨56, by decide⟩, false), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c236, some c237, some c256, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c236, c237, c256] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c236 := h 235 (by decide)
  have h1 : Entails.eval a c237 := h 236 (by decide)
  have h2 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨54, by decide⟩, true), (⟨6, by decide⟩, false), (⟨21, by decide⟩, false), (⟨55, by decide⟩, true), (⟨52, by decide⟩, true), (⟨47, by decide⟩, false), (⟨44, by decide⟩, true), (⟨48, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c109, some c358, some c368, some c91, some c106, some c29, some c1, some c113, some c163, some c12, some c188, some c184, some c193, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c76, c109, c358, c368, c91, c106, c29, c1, c113, c163, c12, c188, c184, c193] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c184 := h 183 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c209, some c140, some c54, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c209, c140, c54] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c209 := h 208 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c18, some c547, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c19, c18, c547] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c547 := derived547 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨11, by decide⟩, true), (⟨14, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c589, some c383, some c182, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c589, c383, c182] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c589 := derived589 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨52, by decide⟩, true), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c358, some c166, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c356, c358, c166] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c238, some c359, some c509, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c238, c359, c509] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c238 := h 237 (by decide)
  have h1 : Entails.eval a c359 := h 358 (by decide)
  have h2 : Entails.eval a c509 := derived509 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨47, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨22, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c89, some c24, some c370, some c543, some c252, some c357, some c238, some c375, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c382, c89, c24, c370, c543, c252, c357, c238, c375] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c382 := h 381 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c370 := h 369 (by decide)
  have h4 : Entails.eval a c543 := derived543 a h
  have h5 : Entails.eval a c252 := h 251 (by decide)
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c238 := h 237 (by decide)
  have h8 : Entails.eval a c375 := h 374 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨44, by decide⟩, false), (⟨47, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c368, some c357, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c374, c368, c357] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c73, some c382, some c383, some c368, some c363, some c360, some c372, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c94, c73, c382, c383, c368, c363, c360, c372] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c73 := h 72 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c360 := h 359 (by decide)
  have h7 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨45, by decide⟩, false), (⟨50, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c372, some c82, some c360, some c368, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c374, c372, c82, c360, c368] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c372 := h 371 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c360 := h 359 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨44, by decide⟩, true), (⟨56, by decide⟩, true), (⟨55, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨45, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c364, some c363, some c370, some c375, some c82, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c364, c363, c370, c375, c82] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c364 := h 363 (by decide)
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c370 := h 369 (by decide)
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨45, by decide⟩, false), (⟨21, by decide⟩, true), (⟨53, by decide⟩, false), (⟨17, by decide⟩, false), (⟨50, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c259, some c258, some c38, some c40, some c26, some c112, some c105, some c34, some c710, some c376, some c244, some c711, some c712, some c382, some c75, some c3, some c375, some c170, some c236, some c360, some c260, some c165, some c703, some c283, some c216, some c214, some c54, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c259, c258, c38, c40, c26, c112, c105, c34, c710, c376, c244, c711, c712, c382, c75, c3, c375, c170, c236, c360, c260, c165, c703, c283, c216, c214, c54] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c259 := h 258 (by decide)
  have h1 : Entails.eval a c258 := h 257 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c710 := derived710 a h
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c711 := derived711 a h
  have h12 : Entails.eval a c712 := derived712 a h
  have h13 : Entails.eval a c382 := h 381 (by decide)
  have h14 : Entails.eval a c75 := h 74 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c375 := h 374 (by decide)
  have h17 : Entails.eval a c170 := h 169 (by decide)
  have h18 : Entails.eval a c236 := h 235 (by decide)
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c703 := derived703 a h
  have h23 : Entails.eval a c283 := h 282 (by decide)
  have h24 : Entails.eval a c216 := h 215 (by decide)
  have h25 : Entails.eval a c214 := h 213 (by decide)
  have h26 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c214, some c54, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c216, c214, c54] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨2, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c509, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c109, c110, c509] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c509 := derived509 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, true), (⟨52, by decide⟩, false), (⟨15, by decide⟩, false), (⟨47, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨44, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c242, some c236, some c30, some c123, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c253, c242, c236, c30, c123] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c242 := h 241 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c205, some c277, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c208, c205, c277] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c46, some c145, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c48, c46, c145] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨29, by decide⟩, false), (⟨49, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c94, some c34, some c107, some c44, some c558, some c206, some c57, some c286, some c25, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c75, c94, c34, c107, c44, c558, c206, c57, c286, c25] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c94 := h 93 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c558 := derived558 a h
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨56, by decide⟩, true), (⟨53, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, true), (⟨11, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c130, some c140, some c306, some c141, some c191, some c8, some c110, some c64, some c136, some c159, some c345, some c203, some c254, some c123, some c115, some c719, some c108, some c61, some c199, some c218, some c314, some c272, some c428, some c343, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c130, c140, c306, c141, c191, c8, c110, c64, c136, c159, c345, c203, c254, c123, c115, c719, c108, c61, c199, c218, c314, c272, c428, c343] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c130 := h 129 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c306 := h 305 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c115 := h 114 (by decide)
  have h15 : Entails.eval a c719 := derived719 a h
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  have h18 : Entails.eval a c199 := h 198 (by decide)
  have h19 : Entails.eval a c218 := h 217 (by decide)
  have h20 : Entails.eval a c314 := h 313 (by decide)
  have h21 : Entails.eval a c272 := h 271 (by decide)
  have h22 : Entails.eval a c428 := derived428 a h
  have h23 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c199, some c206, some c66, some c25, some c325, some c277, some c230, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c45, c199, c206, c66, c25, c325, c277, c230] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c325 := h 324 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  have h7 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨56, by decide⟩, true), (⟨53, by decide⟩, false), (⟨9, by decide⟩, false), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨49, by decide⟩, true), (⟨11, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c720, some c191, some c8, some c110, some c48, some c136, some c147, some c64, some c306, some c152, some c345, some c203, some c254, some c123, some c115, some c721, some c75, some c94, some c34, some c107, some c60, some c558, some c218, some c41, some c325, some c25, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c720, c191, c8, c110, c48, c136, c147, c64, c306, c152, c345, c203, c254, c123, c115, c721, c75, c94, c34, c107, c60, c558, c218, c41, c325, c25] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c720 := derived720 a h
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c115 := h 114 (by decide)
  have h15 : Entails.eval a c721 := derived721 a h
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c34 := h 33 (by decide)
  have h19 : Entails.eval a c107 := h 106 (by decide)
  have h20 : Entails.eval a c60 := h 59 (by decide)
  have h21 : Entails.eval a c558 := derived558 a h
  have h22 : Entails.eval a c218 := h 217 (by decide)
  have h23 : Entails.eval a c41 := h 40 (by decide)
  have h24 : Entails.eval a c325 := h 324 (by decide)
  have h25 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c152, some c345, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c153, c152, c345] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨34, by decide⟩, false), (⟨15, by decide⟩, true), (⟨26, by decide⟩, false), (⟨56, by decide⟩, true), (⟨10, by decide⟩, true), (⟨49, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c94, some c99, some c107, some c106, some c13, some c20, some c98, some c48, some c64, some c136, some c204, some c590, some c127, some c299, some c338, some c202, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c94, c99, c107, c106, c13, c20, c98, c48, c64, c136, c204, c590, c127, c299, c338, c202] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c94 := h 93 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c590 := derived590 a h
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c299 := h 298 (by decide)
  have h14 : Entails.eval a c338 := h 337 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨35, by decide⟩, true), (⟨2, by decide⟩, false), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c64, some c48, some c271, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c64, c48, c271] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c64 := h 63 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨16, by decide⟩, false), (⟨48, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c78, some c175, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c6, c78, c175] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨4, by decide⟩, true), (⟨26, by decide⟩, false), (⟨8, by decide⟩, true), (⟨49, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c8, some c101, some c284, some c726, some c380, some c177, some c356, some c164, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c80, c8, c101, c284, c726, c380, c177, c356, c164] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c726 := derived726 a h
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c177 := h 176 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c376, some c108, some c61, some c45, some c271, some c313, some c270, some c63, some c727, some c589, some c308, some c300, some c6, some c135, some c590, some c345, some c159, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c723, c376, c108, c61, c45, c271, c313, c270, c63, c727, c589, c308, c300, c6, c135, c590, c345, c159] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c313 := h 312 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c727 := derived727 a h
  have h10 : Entails.eval a c589 := derived589 a h
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c135 := h 134 (by decide)
  have h15 : Entails.eval a c590 := derived590 a h
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨43, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c125, some c24, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c169, c125, c24] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c723, some c383, some c376, some c728, some c75, some c3, some c99, some c589, some c98, some c109, some c47, some c63, some c134, some c202, some c729, some c17, some c590, some c127, some c300, some c204, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c723, c383, c376, c728, c75, c3, c99, c589, c98, c109, c47, c63, c134, c202, c729, c17, c590, c127, c300, c204] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c723 := derived723 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c728 := derived728 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c589 := derived589 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c729 := derived729 a h
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c590 := derived590 a h
  have h17 : Entails.eval a c127 := h 126 (by decide)
  have h18 : Entails.eval a c300 := h 299 (by decide)
  have h19 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c140, some c141, some c306, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c140, c141, c306] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c140 := h 139 (by decide)
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c306 := h 305 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨34, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c590, some c339, some c99, some c80, some c108, some c61, some c45, some c175, some c101, some c270, some c380, some c47, some c78, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c353, c590, c339, c99, c80, c108, c61, c45, c175, c101, c270, c380, c47, c78] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c590 := derived590 a h
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨40, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨34, by decide⟩, false), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c383, some c376, some c306, some c133, some c345, some c160, some c732, some c8, some c147, some c308, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c353, c383, c376, c306, c133, c345, c160, c732, c8, c147, c308] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c732 := derived732 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c723, some c383, some c376, some c730, some c353, some c733, some c135, some c347, some c345, some c8, some c158, some c732, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c731, c723, c383, c376, c730, c353, c733, c135, c347, c345, c8, c158, c732] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c730 := derived730 a h
  have h5 : Entails.eval a c353 := h 352 (by decide)
  have h6 : Entails.eval a c733 := derived733 a h
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c347 := h 346 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c732 := derived732 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨26, by decide⟩, false), (⟨34, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c45, some c725, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c61, c45, c725] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c725 := derived725 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c731, some c723, some c383, some c376, some c734, some c110, some c735, some c724, some c98, some c589, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c731, c723, c383, c376, c734, c110, c735, c724, c98, c589] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c731 := derived731 a h
  have h1 : Entails.eval a c723 := derived723 a h
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c734 := derived734 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c735 := derived735 a h
  have h7 : Entails.eval a c724 := derived724 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c589 := derived589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c376, some c736, some c12, some c13, some c112, some c105, some c94, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c383, c376, c736, c12, c13, c112, c105, c94] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c736 := derived736 a h
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨42, by decide⟩, false), (⟨7, by decide⟩, true), (⟨47, by decide⟩, true), (⟨3, by decide⟩, true), (⟨50, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c371, some c98, some c92, some c381, some c380, some c373, some c364, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c75, c371, c98, c92, c381, c380, c373, c364] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  have h7 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨5, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c3, some c94, some c171, some c105, some c27, some c85, some c123, some c738, some c106, some c99, some c35, some c256, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c75, c3, c94, c171, c105, c27, c85, c123, c738, c106, c99, c35, c256] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c738 := derived738 a h
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c171, some c85, some c88, some c371, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c171, c85, c88, c371] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c171 := h 170 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c361, some c357, some c509, some c369, some c22, some c28, some c248, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c361, c357, c509, c369, c22, c28, c248] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c361 := h 360 (by decide)
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c509 := derived509 a h
  have h3 : Entails.eval a c369 := h 368 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨16, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c143, some c50, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c147, c143, c50] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c345, some c159, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c347, c345, c159] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c345 := h 344 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c376, some c383, some c737, some c2, some c739, some c111, some c112, some c589, some c741, some c740, some c178, some c191, some c742, some c300, some c130, some c140, some c50, some c339, some c131, some c159, some c66, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c12, c376, c383, c737, c2, c739, c111, c112, c589, c741, c740, c178, c191, c742, c300, c130, c140, c50, c339, c131, c159, c66] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c589 := derived589 a h
  have h9 : Entails.eval a c741 := derived741 a h
  have h10 : Entails.eval a c740 := derived740 a h
  have h11 : Entails.eval a c178 := h 177 (by decide)
  have h12 : Entails.eval a c191 := h 190 (by decide)
  have h13 : Entails.eval a c742 := derived742 a h
  have h14 : Entails.eval a c300 := h 299 (by decide)
  have h15 : Entails.eval a c130 := h 129 (by decide)
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c50 := h 49 (by decide)
  have h18 : Entails.eval a c339 := h 338 (by decide)
  have h19 : Entails.eval a c131 := h 130 (by decide)
  have h20 : Entails.eval a c159 := h 158 (by decide)
  have h21 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c12, some c376, some c383, some c737, some c2, some c739, some c111, some c112, some c744, some c80, some c8, some c101, some c176, some c380, some c85, some c88, some c509, some c371, some c361, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c12, c376, c383, c737, c2, c739, c111, c112, c744, c80, c8, c101, c176, c380, c85, c88, c509, c371, c361] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c744 := derived744 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c509 := derived509 a h
  have h17 : Entails.eval a c371 := h 370 (by decide)
  have h18 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c178, some c740, some c362, some c357, some c176, some c369, some c92, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c191, c178, c740, c362, c357, c176, c369, c92] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c740 := derived740 a h
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨6, by decide⟩, true), (⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c183, some c740, some c362, some c357, some c369, some c370, some c92, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c746, c183, c740, c362, c357, c369, c370, c92] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c740 := derived740 a h
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨46, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c85, some c88, some c372, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c85, c88, c372] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨45, by decide⟩, true), (⟨48, by decide⟩, true), (⟨56, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c24, some c246, some c252, some c33, some c239, some c256, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c76, c24, c246, c252, c33, c239, c256] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c246 := h 245 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c239 := h 238 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨46, by decide⟩, false), (⟨14, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c748, some c383, some c376, some c357, some c369, some c368, some c749, some c372, some c173, some c22, some c4, some c248, some c246, some c239, some c235, some c36, some c264, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c748, c383, c376, c357, c369, c368, c749, c372, c173, c22, c4, c248, c246, c239, c235, c36, c264] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c748 := derived748 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c369 := h 368 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c749 := derived749 a h
  have h7 : Entails.eval a c372 := h 371 (by decide)
  have h8 : Entails.eval a c173 := h 172 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c246 := h 245 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c36 := h 35 (by decide)
  have h16 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c737, some c2, some c12, some c739, some c112, some c111, some c745, some c106, some c747, some c589, some c6, some c78, some c750, some c748, some c171, some c178, some c743, some c742, some c44, some c308, some c300, some c203, some c130, some c115, some c339, some c197, some c159, some c57, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c376, c383, c737, c2, c12, c739, c112, c111, c745, c106, c747, c589, c6, c78, c750, c748, c171, c178, c743, c742, c44, c308, c300, c203, c130, c115, c339, c197, c159, c57] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c745 := derived745 a h
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c747 := derived747 a h
  have h11 : Entails.eval a c589 := derived589 a h
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c750 := derived750 a h
  have h15 : Entails.eval a c748 := derived748 a h
  have h16 : Entails.eval a c171 := h 170 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c743 := derived743 a h
  have h19 : Entails.eval a c742 := derived742 a h
  have h20 : Entails.eval a c44 := h 43 (by decide)
  have h21 : Entails.eval a c308 := h 307 (by decide)
  have h22 : Entails.eval a c300 := h 299 (by decide)
  have h23 : Entails.eval a c203 := h 202 (by decide)
  have h24 : Entails.eval a c130 := h 129 (by decide)
  have h25 : Entails.eval a c115 := h 114 (by decide)
  have h26 : Entails.eval a c339 := h 338 (by decide)
  have h27 : Entails.eval a c197 := h 196 (by decide)
  have h28 : Entails.eval a c159 := h 158 (by decide)
  have h29 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c745, some c12, some c376, some c383, some c737, some c2, some c739, some c111, some c112, some c106, some c747, some c589, some c6, some c78, some c748, some c750, some c171, some c178, some c751, some c191, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c745, c12, c376, c383, c737, c2, c739, c111, c112, c106, c747, c589, c6, c78, c748, c750, c171, c178, c751, c191] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c745 := derived745 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c737 := derived737 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c739 := derived739 a h
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c747 := derived747 a h
  have h11 : Entails.eval a c589 := derived589 a h
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  have h14 : Entails.eval a c748 := derived748 a h
  have h15 : Entails.eval a c750 := derived750 a h
  have h16 : Entails.eval a c171 := h 170 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c751 := derived751 a h
  have h19 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c737, some c383, some c376, some c2, some c12, some c739, some c112, some c111, some c752, some c1, some c73, some c95, some c163, some c380, some c85, some c88, some c748, some c371, some c361, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c737, c383, c376, c2, c12, c739, c112, c111, c752, c1, c73, c95, c163, c380, c85, c88, c748, c371, c361] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c737 := derived737 a h
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c752 := derived752 a h
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c380 := h 379 (by decide)
  have h14 : Entails.eval a c85 := h 84 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c748 := derived748 a h
  have h17 : Entails.eval a c371 := h 370 (by decide)
  have h18 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨44, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c374, some c371, some c232, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c374, c371, c232] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c374 := h 373 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c94, some c108, some c95, some c380, some c1, some c73, some c163, some c27, some c88, some c254, some c115, some c31, some c246, some c754, some c361, some c162, some c369, some c6, some c362, some c110, some c256, some c28, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c376, c383, c94, c108, c95, c380, c1, c73, c163, c27, c88, c254, c115, c31, c246, c754, c361, c162, c369, c6, c362, c110, c256, c28] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c163 := h 162 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c254 := h 253 (by decide)
  have h12 : Entails.eval a c115 := h 114 (by decide)
  have h13 : Entails.eval a c31 := h 30 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  have h15 : Entails.eval a c754 := derived754 a h
  have h16 : Entails.eval a c361 := h 360 (by decide)
  have h17 : Entails.eval a c162 := h 161 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c6 := h 5 (by decide)
  have h20 : Entails.eval a c362 := h 361 (by decide)
  have h21 : Entails.eval a c110 := h 109 (by decide)
  have h22 : Entails.eval a c256 := h 255 (by decide)
  have h23 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨53, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c376, some c94, some c1, some c73, some c108, some c191, some c95, some c380, some c755, some c112, some c19, some c110, some c6, some c78, some c162, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c383, c376, c94, c1, c73, c108, c191, c95, c380, c755, c112, c19, c110, c6, c78, c162] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c380 := h 379 (by decide)
  have h9 : Entails.eval a c755 := derived755 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c6 := h 5 (by decide)
  have h14 : Entails.eval a c78 := h 77 (by decide)
  have h15 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨48, by decide⟩, true), (⟨42, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c383, some c376, some c89, some c91, some c80, some c28, some c709, some c256, some c248, some c233, some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c383, c376, c89, c91, c80, c28, c709, c256, c248, c233] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c383 := h 382 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c89 := h 88 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c709 := derived709 a h
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨21, by decide⟩, false), (⟨52, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c345, some c343, some c384, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c345, c343, c384] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c345 := h 344 (by decide)
  have h1 : Entails.eval a c343 := h 342 (by decide)
  have h2 : Entails.eval a c384 := derived384 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c158, some c152, some c63, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c158, c152, c63] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨43, by decide⟩, false), (⟨47, by decide⟩, true), (⟨42, by decide⟩, true), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨15, by decide⟩, false), (⟨53, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c758, some c39, some c25, some c128, some c374, some c236, some c233, some c246, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c758, c39, c25, c128, c374, c236, c233, c246] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c758 := derived758 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c374 := h 373 (by decide)
  have h5 : Entails.eval a c236 := h 235 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c76, some c4, some c169, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c76, c4, c169] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c737, some c753, some c756, some c105, some c107, some c19, some c191, some c178, some c509, some c757, some c176, some c175, some c369, some c357, some c761, some c18, some c760, some c759, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c376, c383, c737, c753, c756, c105, c107, c19, c191, c178, c509, c757, c176, c175, c369, c357, c761, c18, c760, c759] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c756 := derived756 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c509 := derived509 a h
  have h11 : Entails.eval a c757 := derived757 a h
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c369 := h 368 (by decide)
  have h15 : Entails.eval a c357 := h 356 (by decide)
  have h16 : Entails.eval a c761 := derived761 a h
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c760 := derived760 a h
  have h19 : Entails.eval a c759 := derived759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨43, by decide⟩, false), (⟨6, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c152, some c759, some c304, some c63, some c337, some c200, some c132, some c252, some c729, some c226, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c133, c152, c759, c304, c63, c337, c200, c132, c252, c729, c226] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c759 := derived759 a h
  have h3 : Entails.eval a c304 := h 303 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c200 := h 199 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c729 := derived729 a h
  have h10 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c762, some c376, some c383, some c737, some c753, some c756, some c105, some c107, some c19, some c191, some c178, some c380, some c78, some c361, some c171, some c763, some c345, some c758, some c760, some c39, some c371, some c128, some c24, some c203, some c240, some c246, some c306, some c127, some c208, some c146, some c47, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c762, c376, c383, c737, c753, c756, c105, c107, c19, c191, c178, c380, c78, c361, c171, c763, c345, c758, c760, c39, c371, c128, c24, c203, c240, c246, c306, c127, c208, c146, c47] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c762 := derived762 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c753 := derived753 a h
  have h5 : Entails.eval a c756 := derived756 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c191 := h 190 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c78 := h 77 (by decide)
  have h13 : Entails.eval a c361 := h 360 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c763 := derived763 a h
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c758 := derived758 a h
  have h18 : Entails.eval a c760 := derived760 a h
  have h19 : Entails.eval a c39 := h 38 (by decide)
  have h20 : Entails.eval a c371 := h 370 (by decide)
  have h21 : Entails.eval a c128 := h 127 (by decide)
  have h22 : Entails.eval a c24 := h 23 (by decide)
  have h23 : Entails.eval a c203 := h 202 (by decide)
  have h24 : Entails.eval a c240 := h 239 (by decide)
  have h25 : Entails.eval a c246 := h 245 (by decide)
  have h26 : Entails.eval a c306 := h 305 (by decide)
  have h27 : Entails.eval a c127 := h 126 (by decide)
  have h28 : Entails.eval a c208 := h 207 (by decide)
  have h29 : Entails.eval a c146 := h 145 (by decide)
  have h30 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c737, some c753, some c756, some c105, some c107, some c19, some c191, some c178, some c762, some c764, some c101, some c761, some c589, some c361, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c376, c383, c737, c753, c756, c105, c107, c19, c191, c178, c762, c764, c101, c761, c589, c361] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c756 := derived756 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c762 := derived762 a h
  have h11 : Entails.eval a c764 := derived764 a h
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c761 := derived761 a h
  have h14 : Entails.eval a c589 := derived589 a h
  have h15 : Entails.eval a c361 := h 360 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c737, some c753, some c756, some c383, some c107, some c765, some c108, some c109, some c99, some c98, some c589, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c737, c753, c756, c383, c107, c765, c108, c109, c99, c98, c589] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c737 := derived737 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c756 := derived756 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c765 := derived765 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c589 := derived589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c753, some c737, some c383, some c376, some c108, some c109, some c75, some c3, some c98, some c171, some c381, some c380, some c92, some c722, some c179, some c169, some c364, some c358, some c369, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c766, c753, c737, c383, c376, c108, c109, c75, c3, c98, c171, c381, c380, c92, c722, c179, c169, c364, c358, c369] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c381 := h 380 (by decide)
  have h12 : Entails.eval a c380 := h 379 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c722 := derived722 a h
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c364 := h 363 (by decide)
  have h18 : Entails.eval a c358 := h 357 (by decide)
  have h19 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨52, by decide⟩, true), (⟨4, by decide⟩, true), (⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c75, some c3, some c761, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c75, c3, c761] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c75 := h 74 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c761 := derived761 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨56, by decide⟩, true), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c178, some c191, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c183, c178, c191] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c178 := h 177 (by decide)
  have h2 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨50, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c380, some c101, some c110, some c769, some c761, some c357, some c362, some c369, some c370, some c92, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c381, c380, c101, c110, c769, c761, c357, c362, c369, c370, c92] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c769 := derived769 a h
  have h5 : Entails.eval a c761 := derived761 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  have h8 : Entails.eval a c369 := h 368 (by decide)
  have h9 : Entails.eval a c370 := h 369 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨43, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c767, some c4, some c76, some c376, some c383, some c737, some c753, some c766, some c770, some c756, some c357, some c361, some c372, some c173, some c369, some c6, some c759, some c362, some c110, some c345, some c757, some c28, some c57, some c256, some c27, some c203, some c163, some c279, some c129, some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c767, c4, c76, c376, c383, c737, c753, c766, c770, c756, c357, c361, c372, c173, c369, c6, c759, c362, c110, c345, c757, c28, c57, c256, c27, c203, c163, c279, c129] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c767 := derived767 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c383 := h 382 (by decide)
  have h5 : Entails.eval a c737 := derived737 a h
  have h6 : Entails.eval a c753 := derived753 a h
  have h7 : Entails.eval a c766 := derived766 a h
  have h8 : Entails.eval a c770 := derived770 a h
  have h9 : Entails.eval a c756 := derived756 a h
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c361 := h 360 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c173 := h 172 (by decide)
  have h14 : Entails.eval a c369 := h 368 (by decide)
  have h15 : Entails.eval a c6 := h 5 (by decide)
  have h16 : Entails.eval a c759 := derived759 a h
  have h17 : Entails.eval a c362 := h 361 (by decide)
  have h18 : Entails.eval a c110 := h 109 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c757 := derived757 a h
  have h21 : Entails.eval a c28 := h 27 (by decide)
  have h22 : Entails.eval a c57 := h 56 (by decide)
  have h23 : Entails.eval a c256 := h 255 (by decide)
  have h24 : Entails.eval a c27 := h 26 (by decide)
  have h25 : Entails.eval a c203 := h 202 (by decide)
  have h26 : Entails.eval a c163 := h 162 (by decide)
  have h27 : Entails.eval a c279 := h 278 (by decide)
  have h28 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c737, some c753, some c766, some c767, some c770, some c76, some c4, some c768, some c771, some c761, some c178, some c182, some c769, some c191, some c173, some c78, some c110, some c19, some c742, some c300, some c130, some c339, some c61, some c155, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c376, c383, c737, c753, c766, c767, c770, c76, c4, c768, c771, c761, c178, c182, c769, c191, c173, c78, c110, c19, c742, c300, c130, c339, c61, c155] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c766 := derived766 a h
  have h5 : Entails.eval a c767 := derived767 a h
  have h6 : Entails.eval a c770 := derived770 a h
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c768 := derived768 a h
  have h10 : Entails.eval a c771 := derived771 a h
  have h11 : Entails.eval a c761 := derived761 a h
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c182 := h 181 (by decide)
  have h14 : Entails.eval a c769 := derived769 a h
  have h15 : Entails.eval a c191 := h 190 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  have h17 : Entails.eval a c78 := h 77 (by decide)
  have h18 : Entails.eval a c110 := h 109 (by decide)
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c742 := derived742 a h
  have h21 : Entails.eval a c300 := h 299 (by decide)
  have h22 : Entails.eval a c130 := h 129 (by decide)
  have h23 : Entails.eval a c339 := h 338 (by decide)
  have h24 : Entails.eval a c61 := h 60 (by decide)
  have h25 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨39, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c772, some c308, some c300, some c130, some c140, some c337, some c304, some c272, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c772, c308, c300, c130, c140, c337, c304, c272] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c772 := derived772 a h
  have h1 : Entails.eval a c308 := h 307 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c337 := h 336 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨56, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c772, some c743, some c773, some c136, some c147, some c339, some c306, some c304, some c152, some c272, some c343, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c772, c743, c773, c136, c147, c339, c306, c304, c152, c272, c343] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c772 := derived772 a h
  have h1 : Entails.eval a c743 := derived743 a h
  have h2 : Entails.eval a c773 := derived773 a h
  have h3 : Entails.eval a c136 := h 135 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c339 := h 338 (by decide)
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨56, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c766, some c737, some c376, some c383, some c774, some c191, some c178, some c171, some c27, some c256, some c767, some c88, some c772, some c753, some c763, some c758, some c754, some c522, some c246, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c766, c737, c376, c383, c774, c191, c178, c171, c27, c256, c767, c88, c772, c753, c763, c758, c754, c522, c246] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c766 := derived766 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c383 := h 382 (by decide)
  have h4 : Entails.eval a c774 := derived774 a h
  have h5 : Entails.eval a c191 := h 190 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c171 := h 170 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c256 := h 255 (by decide)
  have h10 : Entails.eval a c767 := derived767 a h
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c772 := derived772 a h
  have h13 : Entails.eval a c753 := derived753 a h
  have h14 : Entails.eval a c763 := derived763 a h
  have h15 : Entails.eval a c758 := derived758 a h
  have h16 : Entails.eval a c754 := derived754 a h
  have h17 : Entails.eval a c522 := derived522 a h
  have h18 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c383, some c737, some c753, some c766, some c767, some c770, some c774, some c191, some c178, some c171, some c27, some c88, some c256, some c374, some c775, some c254, some c239, some c726, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c376, c383, c737, c753, c766, c767, c770, c774, c191, c178, c171, c27, c88, c256, c374, c775, c254, c239, c726] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c383 := h 382 (by decide)
  have h2 : Entails.eval a c737 := derived737 a h
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c766 := derived766 a h
  have h5 : Entails.eval a c767 := derived767 a h
  have h6 : Entails.eval a c770 := derived770 a h
  have h7 : Entails.eval a c774 := derived774 a h
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c256 := h 255 (by decide)
  have h14 : Entails.eval a c374 := h 373 (by decide)
  have h15 : Entails.eval a c775 := derived775 a h
  have h16 : Entails.eval a c254 := h 253 (by decide)
  have h17 : Entails.eval a c239 := h 238 (by decide)
  have h18 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨5, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨52, by decide⟩, false), (⟨1, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c343, some c57, some c151, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c343, c57, c151] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c343 := h 342 (by decide)
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c772, some c767, some c766, some c737, some c753, some c756, some c383, some c376, some c776, some c769, some c722, some c171, some c27, some c88, some c254, some c374, some c169, some c25, some c777, some c133, some c41, some c304, some c139, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c772, c767, c766, c737, c753, c756, c383, c376, c776, c769, c722, c171, c27, c88, c254, c374, c169, c25, c777, c133, c41, c304, c139] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c772 := derived772 a h
  have h1 : Entails.eval a c767 := derived767 a h
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c753 := derived753 a h
  have h5 : Entails.eval a c756 := derived756 a h
  have h6 : Entails.eval a c383 := h 382 (by decide)
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c776 := derived776 a h
  have h9 : Entails.eval a c769 := derived769 a h
  have h10 : Entails.eval a c722 := derived722 a h
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c254 := h 253 (by decide)
  have h15 : Entails.eval a c374 := h 373 (by decide)
  have h16 : Entails.eval a c169 := h 168 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c777 := derived777 a h
  have h19 : Entails.eval a c133 := h 132 (by decide)
  have h20 : Entails.eval a c41 := h 40 (by decide)
  have h21 : Entails.eval a c304 := h 303 (by decide)
  have h22 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨21, by decide⟩, true), (⟨42, by decide⟩, true), (⟨56, by decide⟩, false), (⟨48, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c232, some c248, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c239, c232, c248] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨56, by decide⟩, false), (⟨48, by decide⟩, true), (⟨43, by decide⟩, true), (⟨15, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c256, some c235, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c123, c256, c235] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c781 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f781 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c753, some c737, some c383, some c376, some c766, some c767, some c770, some c772, some c778, some c357, some c361, some c369, some c362, some c774, some c191, some c178, some c780, some c27, some c36, some c368, some c246, some c252, some c239, some c232, some c715, some c6, some c40, some c127, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p781 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked781 : lratChecker f781 p781 = .success := by decide +kernel
theorem unsat781 : Unsatisfiable (PosFin 57) f781 := by
  apply lratCheckerSound f781 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p781
  · intro a ha; simp [p781] at ha; subst a; trivial
  · exact checked781
theorem derived781 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c781 := by
  apply localUnsat_implies_entails f781 [c753, c737, c383, c376, c766, c767, c770, c772, c778, c357, c361, c369, c362, c774, c191, c178, c780, c27, c36, c368, c246, c252, c239, c232, c715, c6, c40, c127] c781 unsat781 (by rfl) a
  have h0 : Entails.eval a c753 := derived753 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c383 := h 382 (by decide)
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c766 := derived766 a h
  have h5 : Entails.eval a c767 := derived767 a h
  have h6 : Entails.eval a c770 := derived770 a h
  have h7 : Entails.eval a c772 := derived772 a h
  have h8 : Entails.eval a c778 := derived778 a h
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c369 := h 368 (by decide)
  have h12 : Entails.eval a c362 := h 361 (by decide)
  have h13 : Entails.eval a c774 := derived774 a h
  have h14 : Entails.eval a c191 := h 190 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c780 := derived780 a h
  have h17 : Entails.eval a c27 := h 26 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c368 := h 367 (by decide)
  have h20 : Entails.eval a c246 := h 245 (by decide)
  have h21 : Entails.eval a c252 := h 251 (by decide)
  have h22 : Entails.eval a c239 := h 238 (by decide)
  have h23 : Entails.eval a c232 := h 231 (by decide)
  have h24 : Entails.eval a c715 := derived715 a h
  have h25 : Entails.eval a c6 := h 5 (by decide)
  have h26 : Entails.eval a c40 := h 39 (by decide)
  have h27 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c782 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨43, by decide⟩, true), (⟨9, by decide⟩, false), (⟨50, by decide⟩, true), (⟨15, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f782 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c163, some c75, some c191, some c589, some c361, some c543, some c162, some c704, some c182, some c112, some c780, some c27, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p782 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked782 : lratChecker f782 p782 = .success := by decide +kernel
theorem unsat782 : Unsatisfiable (PosFin 57) f782 := by
  apply lratCheckerSound f782 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p782
  · intro a ha; simp [p782] at ha; subst a; trivial
  · exact checked782
theorem derived782 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c782 := by
  apply localUnsat_implies_entails f782 [c357, c163, c75, c191, c589, c361, c543, c162, c704, c182, c112, c780, c27] c782 unsat782 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c589 := derived589 a h
  have h5 : Entails.eval a c361 := h 360 (by decide)
  have h6 : Entails.eval a c543 := derived543 a h
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c704 := derived704 a h
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c780 := derived780 a h
  have h12 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c783 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨53, by decide⟩, false), (⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f783 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c781, some c177, some c753, some c737, some c383, some c769, some c722, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p783 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked783 : lratChecker f783 p783 = .success := by decide +kernel
theorem unsat783 : Unsatisfiable (PosFin 57) f783 := by
  apply lratCheckerSound f783 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p783
  · intro a ha; simp [p783] at ha; subst a; trivial
  · exact checked783
theorem derived783 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c783 := by
  apply localUnsat_implies_entails f783 [c376, c781, c177, c753, c737, c383, c769, c722] c783 unsat783 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c781 := derived781 a h
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c753 := derived753 a h
  have h4 : Entails.eval a c737 := derived737 a h
  have h5 : Entails.eval a c383 := h 382 (by decide)
  have h6 : Entails.eval a c769 := derived769 a h
  have h7 : Entails.eval a c722 := derived722 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived783

end CochromaticTwenty.Certificates.B16_2_2
