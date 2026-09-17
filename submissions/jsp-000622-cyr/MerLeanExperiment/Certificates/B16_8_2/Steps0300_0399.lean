import MerLeanExperiment.Certificates.B16_8_2.Steps0200_0299

/-! Generated from the actual pinned b16_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c681 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c1, some c114, some c178, some c250, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c2, c1, c114, c178, c250] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨46, by decide⟩, true), (⟨9, by decide⟩, true), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c253, some c250, some c107, some c362, some c232, some c234, some c80, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c253, c250, c107, c362, c232, c234, c80] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c253 := h 252 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c232 := h 231 (by decide)
  have h5 : Entails.eval a c234 := h 233 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨38, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨36, by decide⟩, false), (⟨31, by decide⟩, false), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c97, some c681, some c149, some c563, some c154, some c129, some c682, some c207, some c218, some c305, some c312, some c302, some c351, some c262, some c362, some c313, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c49, c97, c681, c149, c563, c154, c129, c682, c207, c218, c305, c312, c302, c351, c262, c362, c313] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c681 := derived681 a h
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c563 := derived563 a h
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c682 := derived682 a h
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c218 := h 217 (by decide)
  have h10 : Entails.eval a c305 := h 304 (by decide)
  have h11 : Entails.eval a c312 := h 311 (by decide)
  have h12 : Entails.eval a c302 := h 301 (by decide)
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c262 := h 261 (by decide)
  have h15 : Entails.eval a c362 := h 361 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨8, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c620, some c639, some c97, some c666, some c670, some c671, some c650, some c49, some c673, some c375, some c39, some c60, some c676, some c679, some c680, some c683, some c18, some c309, some c305, some c302, some c197, some c257, some c23, some c34, some c600, some c450, some c495, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c556, c620, c639, c97, c666, c670, c671, c650, c49, c673, c375, c39, c60, c676, c679, c680, c683, c18, c309, c305, c302, c197, c257, c23, c34, c600, c450, c495] c684 unsat684 (by rfl) a
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
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c676 := derived676 a h
  have h14 : Entails.eval a c679 := derived679 a h
  have h15 : Entails.eval a c680 := derived680 a h
  have h16 : Entails.eval a c683 := derived683 a h
  have h17 : Entails.eval a c18 := h 17 (by decide)
  have h18 : Entails.eval a c309 := h 308 (by decide)
  have h19 : Entails.eval a c305 := h 304 (by decide)
  have h20 : Entails.eval a c302 := h 301 (by decide)
  have h21 : Entails.eval a c197 := h 196 (by decide)
  have h22 : Entails.eval a c257 := h 256 (by decide)
  have h23 : Entails.eval a c23 := h 22 (by decide)
  have h24 : Entails.eval a c34 := h 33 (by decide)
  have h25 : Entails.eval a c600 := derived600 a h
  have h26 : Entails.eval a c450 := derived450 a h
  have h27 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨8, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c680, some c650, some c676, some c684, some c207, some c250, some c375, some c556, some c620, some c639, some c666, some c97, some c670, some c39, some c60, some c671, some c49, some c673, some c679, some c683, some c309, some c257, some c23, some c34, some c600, some c450, some c495, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c680, c650, c676, c684, c207, c250, c375, c556, c620, c639, c666, c97, c670, c39, c60, c671, c49, c673, c679, c683, c309, c257, c23, c34, c600, c450, c495] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c680 := derived680 a h
  have h1 : Entails.eval a c650 := derived650 a h
  have h2 : Entails.eval a c676 := derived676 a h
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c250 := h 249 (by decide)
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c620 := derived620 a h
  have h9 : Entails.eval a c639 := derived639 a h
  have h10 : Entails.eval a c666 := derived666 a h
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c670 := derived670 a h
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c60 := h 59 (by decide)
  have h15 : Entails.eval a c671 := derived671 a h
  have h16 : Entails.eval a c49 := h 48 (by decide)
  have h17 : Entails.eval a c673 := derived673 a h
  have h18 : Entails.eval a c679 := derived679 a h
  have h19 : Entails.eval a c683 := derived683 a h
  have h20 : Entails.eval a c309 := h 308 (by decide)
  have h21 : Entails.eval a c257 := h 256 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c34 := h 33 (by decide)
  have h24 : Entails.eval a c600 := derived600 a h
  have h25 : Entails.eval a c450 := derived450 a h
  have h26 : Entails.eval a c495 := derived495 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c676, some c671, some c620, some c639, some c97, some c666, some c670, some c60, some c39, some c650, some c556, some c375, some c49, some c309, some c673, some c679, some c680, some c683, some c684, some c207, some c250, some c685, some c190, some c336, some c677, some c154, some c178, some c563, some c1, some c149, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c676, c671, c620, c639, c97, c666, c670, c60, c39, c650, c556, c375, c49, c309, c673, c679, c680, c683, c684, c207, c250, c685, c190, c336, c677, c154, c178, c563, c1, c149] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c676 := derived676 a h
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c666 := derived666 a h
  have h6 : Entails.eval a c670 := derived670 a h
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c650 := derived650 a h
  have h10 : Entails.eval a c556 := derived556 a h
  have h11 : Entails.eval a c375 := h 374 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c673 := derived673 a h
  have h15 : Entails.eval a c679 := derived679 a h
  have h16 : Entails.eval a c680 := derived680 a h
  have h17 : Entails.eval a c683 := derived683 a h
  have h18 : Entails.eval a c684 := derived684 a h
  have h19 : Entails.eval a c207 := h 206 (by decide)
  have h20 : Entails.eval a c250 := h 249 (by decide)
  have h21 : Entails.eval a c685 := derived685 a h
  have h22 : Entails.eval a c190 := h 189 (by decide)
  have h23 : Entails.eval a c336 := h 335 (by decide)
  have h24 : Entails.eval a c677 := derived677 a h
  have h25 : Entails.eval a c154 := h 153 (by decide)
  have h26 : Entails.eval a c178 := h 177 (by decide)
  have h27 : Entails.eval a c563 := derived563 a h
  have h28 : Entails.eval a c1 := h 0 (by decide)
  have h29 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨53, by decide⟩, true), (⟨46, by decide⟩, false), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c274, some c149, some c1, some c118, some c178, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c274, c149, c1, c118, c178] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c274 := h 273 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨47, by decide⟩, false), (⟨48, by decide⟩, true), (⟨46, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c222, some c207, some c149, some c286, some c1, some c4, some c167, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c17, c222, c207, c149, c286, c1, c4, c167] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c286 := h 285 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨52, by decide⟩, false), (⟨47, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true), (⟨48, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨36, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c70, some c688, some c209, some c189, some c257, some c305, some c687, some c205, some c340, some c309, some c264, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c98, c70, c688, c209, c189, c257, c305, c687, c205, c340, c309, c264] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c688 := derived688 a h
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c257 := h 256 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c687 := derived687 a h
  have h8 : Entails.eval a c205 := h 204 (by decide)
  have h9 : Entails.eval a c340 := h 339 (by decide)
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨46, by decide⟩, false), (⟨24, by decide⟩, true), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true), (⟨1, by decide⟩, false), (⟨5, by decide⟩, false), (⟨30, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c305, some c274, some c687, some c207, some c149, some c250, some c118, some c119, some c116, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c305, c274, c687, c207, c149, c250, c118, c119, c116] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c305 := h 304 (by decide)
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c687 := derived687 a h
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c250 := h 249 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c375, some c620, some c639, some c97, some c650, some c666, some c670, some c39, some c60, some c671, some c676, some c686, some c98, some c70, some c64, some c327, some c325, some c349, some c346, some c80, some c68, some c689, some c690, some c189, some c261, some c17, some c309, some c207, some c205, some c312, some c302, some c286, some c203, some c153, some c245, some c499, some c90, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c556, c375, c620, c639, c97, c650, c666, c670, c39, c60, c671, c676, c686, c98, c70, c64, c327, c325, c349, c346, c80, c68, c689, c690, c189, c261, c17, c309, c207, c205, c312, c302, c286, c203, c153, c245, c499, c90] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c620 := derived620 a h
  have h3 : Entails.eval a c639 := derived639 a h
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c650 := derived650 a h
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c670 := derived670 a h
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c671 := derived671 a h
  have h11 : Entails.eval a c676 := derived676 a h
  have h12 : Entails.eval a c686 := derived686 a h
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c70 := h 69 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c327 := h 326 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  have h18 : Entails.eval a c349 := h 348 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  have h20 : Entails.eval a c80 := h 79 (by decide)
  have h21 : Entails.eval a c68 := h 67 (by decide)
  have h22 : Entails.eval a c689 := derived689 a h
  have h23 : Entails.eval a c690 := derived690 a h
  have h24 : Entails.eval a c189 := h 188 (by decide)
  have h25 : Entails.eval a c261 := h 260 (by decide)
  have h26 : Entails.eval a c17 := h 16 (by decide)
  have h27 : Entails.eval a c309 := h 308 (by decide)
  have h28 : Entails.eval a c207 := h 206 (by decide)
  have h29 : Entails.eval a c205 := h 204 (by decide)
  have h30 : Entails.eval a c312 := h 311 (by decide)
  have h31 : Entails.eval a c302 := h 301 (by decide)
  have h32 : Entails.eval a c286 := h 285 (by decide)
  have h33 : Entails.eval a c203 := h 202 (by decide)
  have h34 : Entails.eval a c153 := h 152 (by decide)
  have h35 : Entails.eval a c245 := h 244 (by decide)
  have h36 : Entails.eval a c499 := derived499 a h
  have h37 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c17, some c97, some c691, some c98, some c20, some c38, some c52, some c304, some c196, some c207, some c344, some c350, some c312, some c57, some c46, some c203, some c262, some c103, some c21, some c60, some c212, some c351, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c189, c17, c97, c691, c98, c20, c38, c52, c304, c196, c207, c344, c350, c312, c57, c46, c203, c262, c103, c21, c60, c212, c351] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c344 := h 343 (by decide)
  have h12 : Entails.eval a c350 := h 349 (by decide)
  have h13 : Entails.eval a c312 := h 311 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c21 := h 20 (by decide)
  have h20 : Entails.eval a c60 := h 59 (by decide)
  have h21 : Entails.eval a c212 := h 211 (by decide)
  have h22 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨21, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c304, some c196, some c207, some c344, some c312, some c47, some c203, some c262, some c103, some c60, some c351, some c348, some c212, some c57, some c21, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c304, c196, c207, c344, c312, c47, c203, c262, c103, c60, c351, c348, c212, c57, c21] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c304 := h 303 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c351 := h 350 (by decide)
  have h11 : Entails.eval a c348 := h 347 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c692, some c189, some c17, some c97, some c691, some c693, some c39, some c52, some c344, some c18, some c219, some c206, some c352, some c262, some c59, some c311, some c103, some c48, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c692, c189, c17, c97, c691, c693, c39, c52, c344, c18, c219, c206, c352, c262, c59, c311, c103, c48] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c692 := derived692 a h
  have h1 : Entails.eval a c189 := h 188 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c693 := derived693 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c352 := h 351 (by decide)
  have h13 : Entails.eval a c262 := h 261 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c311 := h 310 (by decide)
  have h16 : Entails.eval a c103 := h 102 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c691, some c189, some c17, some c692, some c694, some c252, some c254, some c194, some c206, some c208, some c312, some c304, some c47, some c40, some c103, some c344, some c327, some c60, some c81, some c325, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c97, c691, c189, c17, c692, c694, c252, c254, c194, c206, c208, c312, c304, c47, c40, c103, c344, c327, c60, c81, c325] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c691 := derived691 a h
  have h2 : Entails.eval a c189 := h 188 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c692 := derived692 a h
  have h5 : Entails.eval a c694 := derived694 a h
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c312 := h 311 (by decide)
  have h12 : Entails.eval a c304 := h 303 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c103 := h 102 (by decide)
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c327 := h 326 (by decide)
  have h18 : Entails.eval a c60 := h 59 (by decide)
  have h19 : Entails.eval a c81 := h 80 (by decide)
  have h20 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c252, some c691, some c40, some c344, some c346, some c38, some c194, some c447, some c254, some c258, some c197, some c213, some c348, some c266, some c308, some c49, some c199, some c29, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c252, c691, c40, c344, c346, c38, c194, c447, c254, c258, c197, c213, c348, c266, c308, c49, c199, c29] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c691 := derived691 a h
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c447 := derived447 a h
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c213 := h 212 (by decide)
  have h12 : Entails.eval a c348 := h 347 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  have h14 : Entails.eval a c308 := h 307 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨16, by decide⟩, true), (⟨10, by decide⟩, false), (⟨50, by decide⟩, true), (⟨48, by decide⟩, true), (⟨26, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨23, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c103, some c101, some c29, some c79, some c66, some c204, some c368, some c122, some c165, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c103, c101, c29, c79, c66, c204, c368, c122, c165] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c103 := h 102 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c79 := h 78 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c691, some c375, some c252, some c696, some c304, some c39, some c52, some c208, some c436, some c254, some c258, some c235, some c296, some c519, some c124, some c697, some c48, some c81, some c122, some c233, some c107, some c112, some c135, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c691, c375, c252, c696, c304, c39, c52, c208, c436, c254, c258, c235, c296, c519, c124, c697, c48, c81, c122, c233, c107, c112, c135] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c691 := derived691 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c696 := derived696 a h
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c235 := h 234 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  have h13 : Entails.eval a c519 := derived519 a h
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c697 := derived697 a h
  have h16 : Entails.eval a c48 := h 47 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c122 := h 121 (by decide)
  have h19 : Entails.eval a c233 := h 232 (by decide)
  have h20 : Entails.eval a c107 := h 106 (by decide)
  have h21 : Entails.eval a c112 := h 111 (by decide)
  have h22 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨28, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨32, by decide⟩, false), (⟨6, by decide⟩, false), (⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c436, some c296, some c308, some c198, some c259, some c439, some c150, some c519, some c227, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c39, c436, c296, c308, c198, c259, c439, c150, c519, c227] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c436 := derived436 a h
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c308 := h 307 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c259 := h 258 (by decide)
  have h6 : Entails.eval a c439 := derived439 a h
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c519 := derived519 a h
  have h9 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨36, by decide⟩, false), (⟨28, by decide⟩, false), (⟨17, by decide⟩, true), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c198, some c348, some c311, some c308, some c264, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c215, c198, c348, c311, c308, c264] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c348 := h 347 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨31, by decide⟩, true), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c344, some c345, some c219, some c40, some c691, some c52, some c375, some c48, some c61, some c700, some c260, some c208, some c699, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c39, c344, c345, c219, c40, c691, c52, c375, c48, c61, c700, c260, c208, c699] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c219 := h 218 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c691 := derived691 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c700 := derived700 a h
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c699 := derived699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c695, some c698, some c691, some c375, some c39, some c52, some c344, some c345, some c40, some c219, some c17, some c701, some c103, some c101, some c28, some c59, some c45, some c217, some c199, some c339, some c296, some c700, some c439, some c67, some c66, some c260, some c519, some c225, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c97, c695, c698, c691, c375, c39, c52, c344, c345, c40, c219, c17, c701, c103, c101, c28, c59, c45, c217, c199, c339, c296, c700, c439, c67, c66, c260, c519, c225] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c695 := derived695 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c375 := h 374 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c17 := h 16 (by decide)
  have h12 : Entails.eval a c701 := derived701 a h
  have h13 : Entails.eval a c103 := h 102 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c59 := h 58 (by decide)
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c217 := h 216 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c339 := h 338 (by decide)
  have h21 : Entails.eval a c296 := h 295 (by decide)
  have h22 : Entails.eval a c700 := derived700 a h
  have h23 : Entails.eval a c439 := derived439 a h
  have h24 : Entails.eval a c67 := h 66 (by decide)
  have h25 : Entails.eval a c66 := h 65 (by decide)
  have h26 : Entails.eval a c260 := h 259 (by decide)
  have h27 : Entails.eval a c519 := derived519 a h
  have h28 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨32, by decide⟩, true), (⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c101, some c444, some c600, some c197, some c66, some c227, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c196, c101, c444, c600, c197, c66, c227] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c444 := derived444 a h
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c66 := h 65 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c227, some c600, some c66, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c23, c227, c600, c66] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c227 := h 226 (by decide)
  have h2 : Entails.eval a c600 := derived600 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c695, some c97, some c691, some c698, some c702, some c304, some c196, some c344, some c346, some c38, some c194, some c18, some c703, some c60, some c49, some c704, some c197, some c493, some c308, some c47, some c203, some c26, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c695, c97, c691, c698, c702, c304, c196, c344, c346, c38, c194, c18, c703, c60, c49, c704, c197, c493, c308, c47, c203, c26] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c695 := derived695 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c691 := derived691 a h
  have h3 : Entails.eval a c698 := derived698 a h
  have h4 : Entails.eval a c702 := derived702 a h
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c18 := h 17 (by decide)
  have h12 : Entails.eval a c703 := derived703 a h
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c49 := h 48 (by decide)
  have h15 : Entails.eval a c704 := derived704 a h
  have h16 : Entails.eval a c197 := h 196 (by decide)
  have h17 : Entails.eval a c493 := derived493 a h
  have h18 : Entails.eval a c308 := h 307 (by decide)
  have h19 : Entails.eval a c47 := h 46 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c691, some c556, some c375, some c695, some c705, some c98, some c38, some c52, some c346, some c314, some c304, some c149, some c196, some c1, some c134, some c252, some c178, some c380, some c431, some c90, some c342, some c103, some c672, some c60, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c97, c691, c556, c375, c695, c705, c98, c38, c52, c346, c314, c304, c149, c196, c1, c134, c252, c178, c380, c431, c90, c342, c103, c672, c60] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c691 := derived691 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c695 := derived695 a h
  have h5 : Entails.eval a c705 := derived705 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c314 := h 313 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c1 := h 0 (by decide)
  have h15 : Entails.eval a c134 := h 133 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c380 := h 379 (by decide)
  have h19 : Entails.eval a c431 := derived431 a h
  have h20 : Entails.eval a c90 := h 89 (by decide)
  have h21 : Entails.eval a c342 := h 341 (by decide)
  have h22 : Entails.eval a c103 := h 102 (by decide)
  have h23 : Entails.eval a c672 := derived672 a h
  have h24 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨38, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c97, some c314, some c345, some c149, some c672, some c1, some c134, some c60, some c178, some c103, some c380, some c90, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c98, c97, c314, c345, c149, c672, c1, c134, c60, c178, c103, c380, c90] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c672 := derived672 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c134 := h 133 (by decide)
  have h8 : Entails.eval a c60 := h 59 (by decide)
  have h9 : Entails.eval a c178 := h 177 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨31, by decide⟩, false), (⟨6, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c90, some c299, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c46, c90, c299] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c351, some c352, some c60, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c351, c352, c60] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c351 := h 350 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨25, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c40, some c98, some c20, some c38, some c52, some c305, some c271, some c707, some c708, some c103, some c709, some c267, some c210, some c26, some c206, some c258, some c209, some c200, some c349, some c308, some c269, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c97, c40, c98, c20, c38, c52, c305, c271, c707, c708, c103, c709, c267, c210, c26, c206, c258, c209, c200, c349, c308, c269] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c40 := h 39 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c305 := h 304 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  have h8 : Entails.eval a c707 := derived707 a h
  have h9 : Entails.eval a c708 := derived708 a h
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c709 := derived709 a h
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  have h18 : Entails.eval a c200 := h 199 (by decide)
  have h19 : Entails.eval a c349 := h 348 (by decide)
  have h20 : Entails.eval a c308 := h 307 (by decide)
  have h21 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨26, by decide⟩, false), (⟨48, by decide⟩, true), (⟨8, by decide⟩, true), (⟨31, by decide⟩, true), (⟨40, by decide⟩, true), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c48, some c61, some c81, some c308, some c369, some c325, some c266, some c66, some c150, some c339, some c321, some c67, some c151, some c5, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c39, c48, c61, c81, c308, c369, c325, c266, c66, c150, c339, c321, c67, c151, c5] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c325 := h 324 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c321 := h 320 (by decide)
  have h12 : Entails.eval a c67 := h 66 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c252, some c706, some c97, some c691, some c556, some c375, some c710, some c304, some c39, some c52, some c208, some c98, some c254, some c258, some c235, some c436, some c296, some c711, some c103, some c101, some c59, some c79, some c66, some c317, some c209, some c519, some c124, some c697, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c252, c706, c97, c691, c556, c375, c710, c304, c39, c52, c208, c98, c254, c258, c235, c436, c296, c711, c103, c101, c59, c79, c66, c317, c209, c519, c124, c697] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c710 := derived710 a h
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c254 := h 253 (by decide)
  have h13 : Entails.eval a c258 := h 257 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c436 := derived436 a h
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c711 := derived711 a h
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c101 := h 100 (by decide)
  have h20 : Entails.eval a c59 := h 58 (by decide)
  have h21 : Entails.eval a c79 := h 78 (by decide)
  have h22 : Entails.eval a c66 := h 65 (by decide)
  have h23 : Entails.eval a c317 := h 316 (by decide)
  have h24 : Entails.eval a c209 := h 208 (by decide)
  have h25 : Entails.eval a c519 := derived519 a h
  have h26 : Entails.eval a c124 := h 123 (by decide)
  have h27 : Entails.eval a c697 := derived697 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨24, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c712, some c344, some c39, some c304, some c252, some c706, some c691, some c556, some c375, some c103, some c708, some c98, some c101, some c47, some c57, some c600, some c66, some c299, some c350, some c369, some c67, some c194, some c283, some c258, some c447, some c655, some c119, some c127, some c170, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c97, c712, c344, c39, c304, c252, c706, c691, c556, c375, c103, c708, c98, c101, c47, c57, c600, c66, c299, c350, c369, c67, c194, c283, c258, c447, c655, c119, c127, c170] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c712 := derived712 a h
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c252 := h 251 (by decide)
  have h6 : Entails.eval a c706 := derived706 a h
  have h7 : Entails.eval a c691 := derived691 a h
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c708 := derived708 a h
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c600 := derived600 a h
  have h17 : Entails.eval a c66 := h 65 (by decide)
  have h18 : Entails.eval a c299 := h 298 (by decide)
  have h19 : Entails.eval a c350 := h 349 (by decide)
  have h20 : Entails.eval a c369 := h 368 (by decide)
  have h21 : Entails.eval a c67 := h 66 (by decide)
  have h22 : Entails.eval a c194 := h 193 (by decide)
  have h23 : Entails.eval a c283 := h 282 (by decide)
  have h24 : Entails.eval a c258 := h 257 (by decide)
  have h25 : Entails.eval a c447 := derived447 a h
  have h26 : Entails.eval a c655 := derived655 a h
  have h27 : Entails.eval a c119 := h 118 (by decide)
  have h28 : Entails.eval a c127 := h 126 (by decide)
  have h29 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c49, some c47, some c299, some c67, some c283, some c281, some c80, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c49, c47, c299, c67, c283, c281, c80] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c281 := h 280 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨43, by decide⟩, false), (⟨28, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c283, some c281, some c80, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c283, c281, c80] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c283 := h 282 (by decide)
  have h1 : Entails.eval a c281 := h 280 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, false), (⟨46, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c235, some c327, some c194, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c235, c327, c194] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c235 := h 234 (by decide)
  have h1 : Entails.eval a c327 := h 326 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨38, by decide⟩, true), (⟨44, by decide⟩, false), (⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c715, some c321, some c266, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c715, c321, c266] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c715 := derived715 a h
  have h1 : Entails.eval a c321 := h 320 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c706, some c97, some c691, some c252, some c712, some c344, some c39, some c304, some c305, some c713, some c60, some c672, some c49, some c714, some c716, some c81, some c369, some c325, some c38, some c194, some c270, some c443, some c717, some c446, some c709, some c336, some c266, some c66, some c150, some c299, some c5, some c151, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c706, c97, c691, c252, c712, c344, c39, c304, c305, c713, c60, c672, c49, c714, c716, c81, c369, c325, c38, c194, c270, c443, c717, c446, c709, c336, c266, c66, c150, c299, c5, c151] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c691 := derived691 a h
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c713 := derived713 a h
  have h10 : Entails.eval a c60 := h 59 (by decide)
  have h11 : Entails.eval a c672 := derived672 a h
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c714 := derived714 a h
  have h14 : Entails.eval a c716 := derived716 a h
  have h15 : Entails.eval a c81 := h 80 (by decide)
  have h16 : Entails.eval a c369 := h 368 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c194 := h 193 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c443 := derived443 a h
  have h22 : Entails.eval a c717 := derived717 a h
  have h23 : Entails.eval a c446 := derived446 a h
  have h24 : Entails.eval a c709 := derived709 a h
  have h25 : Entails.eval a c336 := h 335 (by decide)
  have h26 : Entails.eval a c266 := h 265 (by decide)
  have h27 : Entails.eval a c66 := h 65 (by decide)
  have h28 : Entails.eval a c150 := h 149 (by decide)
  have h29 : Entails.eval a c299 := h 298 (by decide)
  have h30 : Entails.eval a c5 := h 4 (by decide)
  have h31 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨20, by decide⟩, true), (⟨38, by decide⟩, true), (⟨42, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c691, some c194, some c38, some c196, some c344, some c704, some c39, some c60, some c305, some c270, some c443, some c190, some c336, some c450, some c150, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c691, c194, c38, c196, c344, c704, c39, c60, c305, c270, c443, c190, c336, c450, c150] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c691 := derived691 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c704 := derived704 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c305 := h 304 (by decide)
  have h9 : Entails.eval a c270 := h 269 (by decide)
  have h10 : Entails.eval a c443 := derived443 a h
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c450 := derived450 a h
  have h14 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨21, by decide⟩, false), (⟨36, by decide⟩, false), (⟨40, by decide⟩, true), (⟨31, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c436, some c23, some c260, some c190, some c215, some c348, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c45, c436, c23, c260, c190, c215, c348] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c436 := derived436 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c215 := h 214 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨25, by decide⟩, false), (⟨46, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c369, some c691, some c38, some c194, some c233, some c719, some c304, some c39, some c48, some c344, some c61, some c501, some c720, some c296, some c439, some c150, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c369, c691, c38, c194, c233, c719, c304, c39, c48, c344, c61, c501, c720, c296, c439, c150] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c369 := h 368 (by decide)
  have h1 : Entails.eval a c691 := derived691 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c719 := derived719 a h
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c344 := h 343 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c501 := derived501 a h
  have h12 : Entails.eval a c720 := derived720 a h
  have h13 : Entails.eval a c296 := h 295 (by decide)
  have h14 : Entails.eval a c439 := derived439 a h
  have h15 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c61, some c344, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c60, c61, c344] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c722, some c718, some c706, some c691, some c556, some c375, some c325, some c80, some c81, some c367, some c327, some c370, some c149, some c353, some c196, some c1, some c120, some c296, some c304, some c115, some c52, some c720, some c208, some c681, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c97, c722, c718, c706, c691, c556, c375, c325, c80, c81, c367, c327, c370, c149, c353, c196, c1, c120, c296, c304, c115, c52, c720, c208, c681] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c722 := derived722 a h
  have h2 : Entails.eval a c718 := derived718 a h
  have h3 : Entails.eval a c706 := derived706 a h
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c556 := derived556 a h
  have h6 : Entails.eval a c375 := h 374 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c327 := h 326 (by decide)
  have h12 : Entails.eval a c370 := h 369 (by decide)
  have h13 : Entails.eval a c149 := h 148 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c120 := h 119 (by decide)
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c304 := h 303 (by decide)
  have h20 : Entails.eval a c115 := h 114 (by decide)
  have h21 : Entails.eval a c52 := h 51 (by decide)
  have h22 : Entails.eval a c720 := derived720 a h
  have h23 : Entails.eval a c208 := h 207 (by decide)
  have h24 : Entails.eval a c681 := derived681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c706, some c97, some c691, some c556, some c375, some c722, some c723, some c38, some c721, some c80, some c68, some c81, some c367, some c149, some c1, some c2, some c178, some c340, some c270, some c305, some c300, some c48, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c718, c706, c97, c691, c556, c375, c722, c723, c38, c721, c80, c68, c81, c367, c149, c1, c2, c178, c340, c270, c305, c300, c48] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c722 := derived722 a h
  have h7 : Entails.eval a c723 := derived723 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c721 := derived721 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c367 := h 366 (by decide)
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c1 := h 0 (by decide)
  have h16 : Entails.eval a c2 := h 1 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  have h18 : Entails.eval a c340 := h 339 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c305 := h 304 (by decide)
  have h21 : Entails.eval a c300 := h 299 (by decide)
  have h22 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c718, some c706, some c97, some c691, some c556, some c375, some c724, some c98, some c38, some c52, some c708, some c304, some c305, some c196, some c207, some c344, some c26, some c60, some c203, some c325, some c299, some c80, some c275, some c283, some c354, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c718, c706, c97, c691, c556, c375, c724, c98, c38, c52, c708, c304, c305, c196, c207, c344, c26, c60, c203, c325, c299, c80, c275, c283, c354] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c718 := derived718 a h
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c724 := derived724 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c708 := derived708 a h
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c344 := h 343 (by decide)
  have h16 : Entails.eval a c26 := h 25 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c203 := h 202 (by decide)
  have h19 : Entails.eval a c325 := h 324 (by decide)
  have h20 : Entails.eval a c299 := h 298 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c275 := h 274 (by decide)
  have h23 : Entails.eval a c283 := h 282 (by decide)
  have h24 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c52, some c708, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c52, c708] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c52 := h 51 (by decide)
  have h1 : Entails.eval a c708 := derived708 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨26, by decide⟩, true), (⟨42, by decide⟩, false), (⟨34, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨39, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨40, by decide⟩, false), (⟨31, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c350, some c299, some c450, some c660, some c495, some c250, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c350, c299, c450, c660, c495, c250] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c350 := h 349 (by decide)
  have h1 : Entails.eval a c299 := h 298 (by decide)
  have h2 : Entails.eval a c450 := derived450 a h
  have h3 : Entails.eval a c660 := derived660 a h
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c725, some c556, some c691, some c97, some c103, some c726, some c101, some c98, some c718, some c706, some c375, some c304, some c305, some c196, some c47, some c207, some c344, some c600, some c299, some c28, some c57, some c66, some c67, some c320, some c369, some c277, some c727, some c216, some c260, some c250, some c495, some c140, some c165, some c111, some c184, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c725, c556, c691, c97, c103, c726, c101, c98, c718, c706, c375, c304, c305, c196, c47, c207, c344, c600, c299, c28, c57, c66, c67, c320, c369, c277, c727, c216, c260, c250, c495, c140, c165, c111, c184] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c725 := derived725 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c691 := derived691 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c726 := derived726 a h
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c718 := derived718 a h
  have h9 : Entails.eval a c706 := derived706 a h
  have h10 : Entails.eval a c375 := h 374 (by decide)
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c305 := h 304 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  have h14 : Entails.eval a c47 := h 46 (by decide)
  have h15 : Entails.eval a c207 := h 206 (by decide)
  have h16 : Entails.eval a c344 := h 343 (by decide)
  have h17 : Entails.eval a c600 := derived600 a h
  have h18 : Entails.eval a c299 := h 298 (by decide)
  have h19 : Entails.eval a c28 := h 27 (by decide)
  have h20 : Entails.eval a c57 := h 56 (by decide)
  have h21 : Entails.eval a c66 := h 65 (by decide)
  have h22 : Entails.eval a c67 := h 66 (by decide)
  have h23 : Entails.eval a c320 := h 319 (by decide)
  have h24 : Entails.eval a c369 := h 368 (by decide)
  have h25 : Entails.eval a c277 := h 276 (by decide)
  have h26 : Entails.eval a c727 := derived727 a h
  have h27 : Entails.eval a c216 := h 215 (by decide)
  have h28 : Entails.eval a c260 := h 259 (by decide)
  have h29 : Entails.eval a c250 := h 249 (by decide)
  have h30 : Entails.eval a c495 := derived495 a h
  have h31 : Entails.eval a c140 := h 139 (by decide)
  have h32 : Entails.eval a c165 := h 164 (by decide)
  have h33 : Entails.eval a c111 := h 110 (by decide)
  have h34 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨26, by decide⟩, false), (⟨31, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c97, some c39, some c510, some c495, some c204, some c439, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c196, c97, c39, c510, c495, c204, c439] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c510 := derived510 a h
  have h4 : Entails.eval a c495 := derived495 a h
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c691, some c556, some c375, some c718, some c725, some c103, some c726, some c98, some c101, some c728, some c39, some c45, some c344, some c196, some c59, some c296, some c339, some c352, some c66, some c67, some c219, some c317, some c17, some c28, some c729, some c250, some c208, some c204, some c227, some c439, some c209, some c519, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c97, c691, c556, c375, c718, c725, c103, c726, c98, c101, c728, c39, c45, c344, c196, c59, c296, c339, c352, c66, c67, c219, c317, c17, c28, c729, c250, c208, c204, c227, c439, c209, c519] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c691 := derived691 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c375 := h 374 (by decide)
  have h4 : Entails.eval a c718 := derived718 a h
  have h5 : Entails.eval a c725 := derived725 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c726 := derived726 a h
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c728 := derived728 a h
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c196 := h 195 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c296 := h 295 (by decide)
  have h17 : Entails.eval a c339 := h 338 (by decide)
  have h18 : Entails.eval a c352 := h 351 (by decide)
  have h19 : Entails.eval a c66 := h 65 (by decide)
  have h20 : Entails.eval a c67 := h 66 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  have h22 : Entails.eval a c317 := h 316 (by decide)
  have h23 : Entails.eval a c17 := h 16 (by decide)
  have h24 : Entails.eval a c28 := h 27 (by decide)
  have h25 : Entails.eval a c729 := derived729 a h
  have h26 : Entails.eval a c250 := h 249 (by decide)
  have h27 : Entails.eval a c208 := h 207 (by decide)
  have h28 : Entails.eval a c204 := h 203 (by decide)
  have h29 : Entails.eval a c227 := h 226 (by decide)
  have h30 : Entails.eval a c439 := derived439 a h
  have h31 : Entails.eval a c209 := h 208 (by decide)
  have h32 : Entails.eval a c519 := derived519 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, true), (⟨3, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c39, some c45, some c344, some c40, some c59, some c296, some c339, some c66, some c67, some c170, some c368, some c323, some c143, some c164, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c375, c39, c45, c344, c40, c59, c296, c339, c66, c67, c170, c368, c323, c143, c164] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c368 := h 367 (by decide)
  have h12 : Entails.eval a c323 := h 322 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c375, some c103, some c101, some c13, some c731, some c304, some c40, some c47, some c344, some c600, some c299, some c57, some c66, some c169, some c67, some c320, some c368, some c140, some c165, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c375, c103, c101, c13, c731, c304, c40, c47, c344, c600, c299, c57, c66, c169, c67, c320, c368, c140, c165] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c375 := h 374 (by decide)
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c731 := derived731 a h
  have h5 : Entails.eval a c304 := h 303 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c600 := derived600 a h
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c66 := h 65 (by decide)
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c368 := h 367 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c169, some c7, some c57, some c66, some c320, some c318, some c81, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c169, c7, c57, c66, c320, c318, c81] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c169 := h 168 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨41, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c81, some c367, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c80, c81, c367] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨34, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, false), (⟨28, by decide⟩, false), (⟨31, by decide⟩, false), (⟨44, by decide⟩, false), (⟨46, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c70, some c278, some c368, some c190, some c358, some c23, some c21, some c299, some c202, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c70, c278, c368, c190, c358, c23, c21, c299, c202] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c299 := h 298 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨28, by decide⟩, false), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false), (⟨9, by decide⟩, true), (⟨46, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c380, some c376, some c362, some c171, some c284, some c324, some c145, some c270, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c154, c380, c376, c362, c171, c284, c324, c145, c270] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c380 := h 379 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c362 := h 361 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c324 := h 323 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c556, some c730, some c70, some c98, some c375, some c154, some c2, some c149, some c732, some c734, some c722, some c691, some c304, some c40, some c49, some c714, some c344, some c733, some c600, some c336, some c7, some c735, some c736, some c499, some c358, some c160, some c371, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c97, c556, c730, c70, c98, c375, c154, c2, c149, c732, c734, c722, c691, c304, c40, c49, c714, c344, c733, c600, c336, c7, c735, c736, c499, c358, c160, c371] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c730 := derived730 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c154 := h 153 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c732 := derived732 a h
  have h10 : Entails.eval a c734 := derived734 a h
  have h11 : Entails.eval a c722 := derived722 a h
  have h12 : Entails.eval a c691 := derived691 a h
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c714 := derived714 a h
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c733 := derived733 a h
  have h19 : Entails.eval a c600 := derived600 a h
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c735 := derived735 a h
  have h23 : Entails.eval a c736 := derived736 a h
  have h24 : Entails.eval a c499 := derived499 a h
  have h25 : Entails.eval a c358 := h 357 (by decide)
  have h26 : Entails.eval a c160 := h 159 (by decide)
  have h27 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c730, some c70, some c98, some c97, some c737, some c39, some c344, some c40, some c154, some c2, some c732, some c48, some c375, some c149, some c734, some c722, some c691, some c296, some c736, some c45, some c358, some c7, some c281, some c321, some c371, some c368, some c35, some c160, some c499, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c556, c730, c70, c98, c97, c737, c39, c344, c40, c154, c2, c732, c48, c375, c149, c734, c722, c691, c296, c736, c45, c358, c7, c281, c321, c371, c368, c35, c160, c499] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c730 := derived730 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c737 := derived737 a h
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c344 := h 343 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c2 := h 1 (by decide)
  have h11 : Entails.eval a c732 := derived732 a h
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c375 := h 374 (by decide)
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c734 := derived734 a h
  have h16 : Entails.eval a c722 := derived722 a h
  have h17 : Entails.eval a c691 := derived691 a h
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c736 := derived736 a h
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c358 := h 357 (by decide)
  have h22 : Entails.eval a c7 := h 6 (by decide)
  have h23 : Entails.eval a c281 := h 280 (by decide)
  have h24 : Entails.eval a c321 := h 320 (by decide)
  have h25 : Entails.eval a c371 := h 370 (by decide)
  have h26 : Entails.eval a c368 := h 367 (by decide)
  have h27 : Entails.eval a c35 := h 34 (by decide)
  have h28 : Entails.eval a c160 := h 159 (by decide)
  have h29 : Entails.eval a c499 := derived499 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c556, some c375, some c97, some c730, some c70, some c154, some c98, some c2, some c149, some c732, some c734, some c737, some c48, some c738, some c169, some c7, some c66, some c45, some c278, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c556, c375, c97, c730, c70, c154, c98, c2, c149, c732, c734, c737, c48, c738, c169, c7, c66, c45, c278] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c556 := derived556 a h
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c730 := derived730 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c732 := derived732 a h
  have h10 : Entails.eval a c734 := derived734 a h
  have h11 : Entails.eval a c737 := derived737 a h
  have h12 : Entails.eval a c48 := h 47 (by decide)
  have h13 : Entails.eval a c738 := derived738 a h
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c7 := h 6 (by decide)
  have h16 : Entails.eval a c66 := h 65 (by decide)
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨50, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c154, some c2, some c577, some c169, some c380, some c7, some c358, some c598, some c368, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c154, c2, c577, c169, c380, c7, c358, c598, c368] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c154 := h 153 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c577 := derived577 a h
  have h3 : Entails.eval a c169 := h 168 (by decide)
  have h4 : Entails.eval a c380 := h 379 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c358 := h 357 (by decide)
  have h7 : Entails.eval a c598 := derived598 a h
  have h8 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c739, some c691, some c556, some c375, some c740, some c369, some c353, some c66, some c366, some c596, some c83, some c722, some c324, some c325, some c37, some c194, some c273, some c284, some c18, some c233, some c199, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c98, c739, c691, c556, c375, c740, c369, c353, c66, c366, c596, c83, c722, c324, c325, c37, c194, c273, c284, c18, c233, c199] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c739 := derived739 a h
  have h2 : Entails.eval a c691 := derived691 a h
  have h3 : Entails.eval a c556 := derived556 a h
  have h4 : Entails.eval a c375 := h 374 (by decide)
  have h5 : Entails.eval a c740 := derived740 a h
  have h6 : Entails.eval a c369 := h 368 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c366 := h 365 (by decide)
  have h10 : Entails.eval a c596 := derived596 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c722 := derived722 a h
  have h13 : Entails.eval a c324 := h 323 (by decide)
  have h14 : Entails.eval a c325 := h 324 (by decide)
  have h15 : Entails.eval a c37 := h 36 (by decide)
  have h16 : Entails.eval a c194 := h 193 (by decide)
  have h17 : Entails.eval a c273 := h 272 (by decide)
  have h18 : Entails.eval a c284 := h 283 (by decide)
  have h19 : Entails.eval a c18 := h 17 (by decide)
  have h20 : Entails.eval a c233 := h 232 (by decide)
  have h21 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c48, some c49, some c304, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c48, c49, c304] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c48 := h 47 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨28, by decide⟩, false), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c304, some c51, some c284, some c302, some c69, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c304, c51, c284, c302, c69] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c304 := h 303 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨44, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c722, some c742, some c743, some c39, some c344, some c63, some c342, some c324, some c69, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c722, c742, c743, c39, c344, c63, c342, c324, c69] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c722 := derived722 a h
  have h1 : Entails.eval a c742 := derived742 a h
  have h2 : Entails.eval a c743 := derived743 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c344 := h 343 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c324 := h 323 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c739, some c556, some c741, some c744, some c596, some c600, some c40, some c304, some c296, some c45, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c98, c739, c556, c741, c744, c596, c600, c40, c304, c296, c45] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c739 := derived739 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c741 := derived741 a h
  have h4 : Entails.eval a c744 := derived744 a h
  have h5 : Entails.eval a c596 := derived596 a h
  have h6 : Entails.eval a c600 := derived600 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c304 := h 303 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c39, some c45, some c344, some c63, some c40, some c342, some c296, some c88, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c39, c45, c344, c63, c40, c342, c296, c88] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c39 := h 38 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c344 := h 343 (by decide)
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c342 := h 341 (by decide)
  have h6 : Entails.eval a c296 := h 295 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c746, some c304, some c40, some c51, some c600, some c302, some c88, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c746, c304, c40, c51, c600, c302, c88] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c746 := derived746 a h
  have h1 : Entails.eval a c304 := h 303 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c600 := derived600 a h
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c556, some c375, some c98, some c745, some c747, some c596, some c734, some c742, some c80, some c68, some c81, some c149, some c583, some c2, some c69, some c154, some c372, some c370, some c354, some c353, some c376, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c739, c556, c375, c98, c745, c747, c596, c734, c742, c80, c68, c81, c149, c583, c2, c69, c154, c372, c370, c354, c353, c376] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c556 := derived556 a h
  have h2 : Entails.eval a c375 := h 374 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c745 := derived745 a h
  have h5 : Entails.eval a c747 := derived747 a h
  have h6 : Entails.eval a c596 := derived596 a h
  have h7 : Entails.eval a c734 := derived734 a h
  have h8 : Entails.eval a c742 := derived742 a h
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c149 := h 148 (by decide)
  have h13 : Entails.eval a c583 := derived583 a h
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c69 := h 68 (by decide)
  have h16 : Entails.eval a c154 := h 153 (by decide)
  have h17 : Entails.eval a c372 := h 371 (by decide)
  have h18 : Entails.eval a c370 := h 369 (by decide)
  have h19 : Entails.eval a c354 := h 353 (by decide)
  have h20 : Entails.eval a c353 := h 352 (by decide)
  have h21 : Entails.eval a c376 := h 375 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c691, some c556, some c748, some c94, some c50, some c52, some c302, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c739, c691, c556, c748, c94, c50, c52, c302] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c691 := derived691 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c748 := derived748 a h
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c68, some c81, some c300, some c327, some c36, some c63, some c340, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c68, c81, c300, c327, c36, c63, c340] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨46, by decide⟩, false), (⟨5, by decide⟩, true), (⟨38, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c750, some c325, some c61, some c36, some c327, some c284, some c83, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c750, c325, c61, c36, c327, c284, c83] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c750 := derived750 a h
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨2, by decide⟩, true), (⟨51, by decide⟩, true), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c325, some c369, some c76, some c371, some c284, some c354, some c314, some c273, some c263, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c325, c369, c76, c371, c284, c354, c314, c273, c263] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c325 := h 324 (by decide)
  have h1 : Entails.eval a c369 := h 368 (by decide)
  have h2 : Entails.eval a c76 := h 75 (by decide)
  have h3 : Entails.eval a c371 := h 370 (by decide)
  have h4 : Entails.eval a c284 := h 283 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c273 := h 272 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c753 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f753 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c749, some c99, some c739, some c344, some c342, some c63, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p753 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked753 : lratChecker f753 p753 = .success := by decide +kernel
theorem unsat753 : Unsatisfiable (PosFin 57) f753 := by
  apply lratCheckerSound f753 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p753
  · intro a ha; simp [p753] at ha; subst a; trivial
  · exact checked753
theorem derived753 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c753 := by
  apply localUnsat_implies_entails f753 [c749, c99, c739, c344, c342, c63] c753 unsat753 (by rfl) a
  have h0 : Entails.eval a c749 := derived749 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c342 := h 341 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c754 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, true), (⟨44, by decide⟩, true), (⟨2, by decide⟩, true), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f754 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c349, some c56, some c340, some c351, some c355, some c210, some c314, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p754 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked754 : lratChecker f754 p754 = .success := by decide +kernel
theorem unsat754 : Unsatisfiable (PosFin 57) f754 := by
  apply lratCheckerSound f754 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p754
  · intro a ha; simp [p754] at ha; subst a; trivial
  · exact checked754
theorem derived754 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c754 := by
  apply localUnsat_implies_entails f754 [c349, c56, c340, c351, c355, c210, c314] c754 unsat754 (by rfl) a
  have h0 : Entails.eval a c349 := h 348 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c340 := h 339 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c755 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f755 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c749, some c99, some c739, some c691, some c556, some c375, some c94, some c50, some c38, some c70, some c380, some c302, some c90, some c751, some c596, some c752, some c753, some c195, some c252, some c19, some c27, some c754, some c268, some c413, some c300, some c404, some c198, some c355, some c276, some c273, some c83, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p755 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked755 : lratChecker f755 p755 = .success := by decide +kernel
theorem unsat755 : Unsatisfiable (PosFin 57) f755 := by
  apply lratCheckerSound f755 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p755
  · intro a ha; simp [p755] at ha; subst a; trivial
  · exact checked755
theorem derived755 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c755 := by
  apply localUnsat_implies_entails f755 [c749, c99, c739, c691, c556, c375, c94, c50, c38, c70, c380, c302, c90, c751, c596, c752, c753, c195, c252, c19, c27, c754, c268, c413, c300, c404, c198, c355, c276, c273, c83] c755 unsat755 (by rfl) a
  have h0 : Entails.eval a c749 := derived749 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c556 := derived556 a h
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c94 := h 93 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c380 := h 379 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c751 := derived751 a h
  have h14 : Entails.eval a c596 := derived596 a h
  have h15 : Entails.eval a c752 := derived752 a h
  have h16 : Entails.eval a c753 := derived753 a h
  have h17 : Entails.eval a c195 := h 194 (by decide)
  have h18 : Entails.eval a c252 := h 251 (by decide)
  have h19 : Entails.eval a c19 := h 18 (by decide)
  have h20 : Entails.eval a c27 := h 26 (by decide)
  have h21 : Entails.eval a c754 := derived754 a h
  have h22 : Entails.eval a c268 := h 267 (by decide)
  have h23 : Entails.eval a c413 := derived413 a h
  have h24 : Entails.eval a c300 := h 299 (by decide)
  have h25 : Entails.eval a c404 := derived404 a h
  have h26 : Entails.eval a c198 := h 197 (by decide)
  have h27 : Entails.eval a c355 := h 354 (by decide)
  have h28 : Entails.eval a c276 := h 275 (by decide)
  have h29 : Entails.eval a c273 := h 272 (by decide)
  have h30 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c756 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f756 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c355, some c13, some c128, some c154, some c114, some c314, some c29, some c211, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p756 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked756 : lratChecker f756 p756 = .success := by decide +kernel
theorem unsat756 : Unsatisfiable (PosFin 57) f756 := by
  apply lratCheckerSound f756 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p756
  · intro a ha; simp [p756] at ha; subst a; trivial
  · exact checked756
theorem derived756 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c756 := by
  apply localUnsat_implies_entails f756 [c152, c355, c13, c128, c154, c114, c314, c29, c211] c756 unsat756 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c314 := h 313 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c757 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨52, by decide⟩, true), (⟨29, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨51, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f757 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c596, some c756, some c752, some c284, some c358, some c76, some c368, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p757 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked757 : lratChecker f757 p757 = .success := by decide +kernel
theorem unsat757 : Unsatisfiable (PosFin 57) f757 := by
  apply lratCheckerSound f757 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p757
  · intro a ha; simp [p757] at ha; subst a; trivial
  · exact checked757
theorem derived757 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c757 := by
  apply localUnsat_implies_entails f757 [c596, c756, c752, c284, c358, c76, c368] c757 unsat757 (by rfl) a
  have h0 : Entails.eval a c596 := derived596 a h
  have h1 : Entails.eval a c756 := derived756 a h
  have h2 : Entails.eval a c752 := derived752 a h
  have h3 : Entails.eval a c284 := h 283 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c758 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨53, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f758 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c250, some c19, some c380, some c99, some c300, some c311, some c404, some c757, some c751, some c61, some c68, some c154, some c346, some c284, some c2, some c189, some c83, some c149, some c276, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p758 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked758 : lratChecker f758 p758 = .success := by decide +kernel
theorem unsat758 : Unsatisfiable (PosFin 57) f758 := by
  apply lratCheckerSound f758 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p758
  · intro a ha; simp [p758] at ha; subst a; trivial
  · exact checked758
theorem derived758 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c758 := by
  apply localUnsat_implies_entails f758 [c250, c19, c380, c99, c300, c311, c404, c757, c751, c61, c68, c154, c346, c284, c2, c189, c83, c149, c276] c758 unsat758 (by rfl) a
  have h0 : Entails.eval a c250 := h 249 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c380 := h 379 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c404 := derived404 a h
  have h7 : Entails.eval a c757 := derived757 a h
  have h8 : Entails.eval a c751 := derived751 a h
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c154 := h 153 (by decide)
  have h12 : Entails.eval a c346 := h 345 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c759 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f759 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c346, some c350, some c211, some c209, some c257, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p759 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked759 : lratChecker f759 p759 = .success := by decide +kernel
theorem unsat759 : Unsatisfiable (PosFin 57) f759 := by
  apply lratCheckerSound f759 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p759
  · intro a ha; simp [p759] at ha; subst a; trivial
  · exact checked759
theorem derived759 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c759 := by
  apply localUnsat_implies_entails f759 [c346, c350, c211, c209, c257] c759 unsat759 (by rfl) a
  have h0 : Entails.eval a c346 := h 345 (by decide)
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c760 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨36, by decide⟩, true), (⟨28, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f760 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c753, some c755, some c749, some c99, some c739, some c691, some c556, some c375, some c272, some c195, some c252, some c19, some c250, some c758, some c206, some c759, some c61, some c217, some c29, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p760 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked760 : lratChecker f760 p760 = .success := by decide +kernel
theorem unsat760 : Unsatisfiable (PosFin 57) f760 := by
  apply lratCheckerSound f760 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p760
  · intro a ha; simp [p760] at ha; subst a; trivial
  · exact checked760
theorem derived760 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c760 := by
  apply localUnsat_implies_entails f760 [c753, c755, c749, c99, c739, c691, c556, c375, c272, c195, c252, c19, c250, c758, c206, c759, c61, c217, c29] c760 unsat760 (by rfl) a
  have h0 : Entails.eval a c753 := derived753 a h
  have h1 : Entails.eval a c755 := derived755 a h
  have h2 : Entails.eval a c749 := derived749 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c739 := derived739 a h
  have h5 : Entails.eval a c691 := derived691 a h
  have h6 : Entails.eval a c556 := derived556 a h
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c195 := h 194 (by decide)
  have h10 : Entails.eval a c252 := h 251 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c250 := h 249 (by decide)
  have h13 : Entails.eval a c758 := derived758 a h
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c759 := derived759 a h
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c217 := h 216 (by decide)
  have h18 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c761 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f761 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c749, some c99, some c739, some c304, some c302, some c51, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p761 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked761 : lratChecker f761 p761 = .success := by decide +kernel
theorem unsat761 : Unsatisfiable (PosFin 57) f761 := by
  apply lratCheckerSound f761 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p761
  · intro a ha; simp [p761] at ha; subst a; trivial
  · exact checked761
theorem derived761 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c761 := by
  apply localUnsat_implies_entails f761 [c749, c99, c739, c304, c302, c51] c761 unsat761 (by rfl) a
  have h0 : Entails.eval a c749 := derived749 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c304 := h 303 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c762 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f762 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c35, some c27, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p762 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked762 : lratChecker f762 p762 = .success := by decide +kernel
theorem unsat762 : Unsatisfiable (PosFin 57) f762 := by
  apply lratCheckerSound f762 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p762
  · intro a ha; simp [p762] at ha; subst a; trivial
  · exact checked762
theorem derived762 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c762 := by
  apply localUnsat_implies_entails f762 [c191, c35, c27] c762 unsat762 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c763 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f763 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c753, some c761, some c195, some c691, some c272, some c380, some c749, some c99, some c739, some c556, some c760, some c349, some c265, some c308, some c762, some c351, some c37, some c56, some c300, some c596, some c751, some c68, some c358, some c321, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p763 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked763 : lratChecker f763 p763 = .success := by decide +kernel
theorem unsat763 : Unsatisfiable (PosFin 57) f763 := by
  apply lratCheckerSound f763 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p763
  · intro a ha; simp [p763] at ha; subst a; trivial
  · exact checked763
theorem derived763 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c763 := by
  apply localUnsat_implies_entails f763 [c753, c761, c195, c691, c272, c380, c749, c99, c739, c556, c760, c349, c265, c308, c762, c351, c37, c56, c300, c596, c751, c68, c358, c321] c763 unsat763 (by rfl) a
  have h0 : Entails.eval a c753 := derived753 a h
  have h1 : Entails.eval a c761 := derived761 a h
  have h2 : Entails.eval a c195 := h 194 (by decide)
  have h3 : Entails.eval a c691 := derived691 a h
  have h4 : Entails.eval a c272 := h 271 (by decide)
  have h5 : Entails.eval a c380 := h 379 (by decide)
  have h6 : Entails.eval a c749 := derived749 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c739 := derived739 a h
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c760 := derived760 a h
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c308 := h 307 (by decide)
  have h14 : Entails.eval a c762 := derived762 a h
  have h15 : Entails.eval a c351 := h 350 (by decide)
  have h16 : Entails.eval a c37 := h 36 (by decide)
  have h17 : Entails.eval a c56 := h 55 (by decide)
  have h18 : Entails.eval a c300 := h 299 (by decide)
  have h19 : Entails.eval a c596 := derived596 a h
  have h20 : Entails.eval a c751 := derived751 a h
  have h21 : Entails.eval a c68 := h 67 (by decide)
  have h22 : Entails.eval a c358 := h 357 (by decide)
  have h23 : Entails.eval a c321 := h 320 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c764 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨36, by decide⟩, false), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f764 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c349, some c250, some c762, some c351, some c37, some c56, some c63, some c212, some c596, some c23, some c751, some c202, some c154, some c256, some c145, some c147, some c113, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p764 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked764 : lratChecker f764 p764 = .success := by decide +kernel
theorem unsat764 : Unsatisfiable (PosFin 57) f764 := by
  apply lratCheckerSound f764 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p764
  · intro a ha; simp [p764] at ha; subst a; trivial
  · exact checked764
theorem derived764 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c764 := by
  apply localUnsat_implies_entails f764 [c349, c250, c762, c351, c37, c56, c63, c212, c596, c23, c751, c202, c154, c256, c145, c147, c113] c764 unsat764 (by rfl) a
  have h0 : Entails.eval a c349 := h 348 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c762 := derived762 a h
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c212 := h 211 (by decide)
  have h8 : Entails.eval a c596 := derived596 a h
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c751 := derived751 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c256 := h 255 (by decide)
  have h14 : Entails.eval a c145 := h 144 (by decide)
  have h15 : Entails.eval a c147 := h 146 (by decide)
  have h16 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c765 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f765 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c761, some c753, some c691, some c272, some c763, some c268, some c349, some c265, some c755, some c749, some c99, some c739, some c556, some c375, some c37, some c56, some c596, some c751, some c49, some c154, some c296, some c2, some c7, some c169, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p765 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked765 : lratChecker f765 p765 = .success := by decide +kernel
theorem unsat765 : Unsatisfiable (PosFin 57) f765 := by
  apply lratCheckerSound f765 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p765
  · intro a ha; simp [p765] at ha; subst a; trivial
  · exact checked765
theorem derived765 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c765 := by
  apply localUnsat_implies_entails f765 [c761, c753, c691, c272, c763, c268, c349, c265, c755, c749, c99, c739, c556, c375, c37, c56, c596, c751, c49, c154, c296, c2, c7, c169] c765 unsat765 (by rfl) a
  have h0 : Entails.eval a c761 := derived761 a h
  have h1 : Entails.eval a c753 := derived753 a h
  have h2 : Entails.eval a c691 := derived691 a h
  have h3 : Entails.eval a c272 := h 271 (by decide)
  have h4 : Entails.eval a c763 := derived763 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c755 := derived755 a h
  have h9 : Entails.eval a c749 := derived749 a h
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c739 := derived739 a h
  have h12 : Entails.eval a c556 := derived556 a h
  have h13 : Entails.eval a c375 := h 374 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c56 := h 55 (by decide)
  have h16 : Entails.eval a c596 := derived596 a h
  have h17 : Entails.eval a c751 := derived751 a h
  have h18 : Entails.eval a c49 := h 48 (by decide)
  have h19 : Entails.eval a c154 := h 153 (by decide)
  have h20 : Entails.eval a c296 := h 295 (by decide)
  have h21 : Entails.eval a c2 := h 1 (by decide)
  have h22 : Entails.eval a c7 := h 6 (by decide)
  have h23 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c766 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f766 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c755, some c749, some c99, some c739, some c691, some c556, some c380, some c753, some c761, some c272, some c195, some c252, some c19, some c763, some c268, some c349, some c265, some c764, some c765, some c351, some c412, some c346, some c209, some c210, some c27, some c256, some c67, some c205, some c277, some c296, some c66, some c150, some c7, some c121, some c174, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p766 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked766 : lratChecker f766 p766 = .success := by decide +kernel
theorem unsat766 : Unsatisfiable (PosFin 57) f766 := by
  apply lratCheckerSound f766 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p766
  · intro a ha; simp [p766] at ha; subst a; trivial
  · exact checked766
theorem derived766 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c766 := by
  apply localUnsat_implies_entails f766 [c755, c749, c99, c739, c691, c556, c380, c753, c761, c272, c195, c252, c19, c763, c268, c349, c265, c764, c765, c351, c412, c346, c209, c210, c27, c256, c67, c205, c277, c296, c66, c150, c7, c121, c174] c766 unsat766 (by rfl) a
  have h0 : Entails.eval a c755 := derived755 a h
  have h1 : Entails.eval a c749 := derived749 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c556 := derived556 a h
  have h6 : Entails.eval a c380 := h 379 (by decide)
  have h7 : Entails.eval a c753 := derived753 a h
  have h8 : Entails.eval a c761 := derived761 a h
  have h9 : Entails.eval a c272 := h 271 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c763 := derived763 a h
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c265 := h 264 (by decide)
  have h17 : Entails.eval a c764 := derived764 a h
  have h18 : Entails.eval a c765 := derived765 a h
  have h19 : Entails.eval a c351 := h 350 (by decide)
  have h20 : Entails.eval a c412 := derived412 a h
  have h21 : Entails.eval a c346 := h 345 (by decide)
  have h22 : Entails.eval a c209 := h 208 (by decide)
  have h23 : Entails.eval a c210 := h 209 (by decide)
  have h24 : Entails.eval a c27 := h 26 (by decide)
  have h25 : Entails.eval a c256 := h 255 (by decide)
  have h26 : Entails.eval a c67 := h 66 (by decide)
  have h27 : Entails.eval a c205 := h 204 (by decide)
  have h28 : Entails.eval a c277 := h 276 (by decide)
  have h29 : Entails.eval a c296 := h 295 (by decide)
  have h30 : Entails.eval a c66 := h 65 (by decide)
  have h31 : Entails.eval a c150 := h 149 (by decide)
  have h32 : Entails.eval a c7 := h 6 (by decide)
  have h33 : Entails.eval a c121 := h 120 (by decide)
  have h34 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c767 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨36, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨53, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f767 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c324, some c154, some c178, some c366, some c370, some c144, some c149, some c353, some c3, some c376, some c164, some c354, some c372, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p767 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked767 : lratChecker f767 p767 = .success := by decide +kernel
theorem unsat767 : Unsatisfiable (PosFin 57) f767 := by
  apply lratCheckerSound f767 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p767
  · intro a ha; simp [p767] at ha; subst a; trivial
  · exact checked767
theorem derived767 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c767 := by
  apply localUnsat_implies_entails f767 [c324, c154, c178, c366, c370, c144, c149, c353, c3, c376, c164, c354, c372] c767 unsat767 (by rfl) a
  have h0 : Entails.eval a c324 := h 323 (by decide)
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c366 := h 365 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c353 := h 352 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c376 := h 375 (by decide)
  have h10 : Entails.eval a c164 := h 163 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c768 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f768 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c766, some c69, some c755, some c749, some c99, some c556, some c375, some c36, some c49, some c324, some c68, some c81, some c767, some c2, some c149, some c577, some c276, some c296, some c587, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p768 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked768 : lratChecker f768 p768 = .success := by decide +kernel
theorem unsat768 : Unsatisfiable (PosFin 57) f768 := by
  apply lratCheckerSound f768 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p768
  · intro a ha; simp [p768] at ha; subst a; trivial
  · exact checked768
theorem derived768 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c768 := by
  apply localUnsat_implies_entails f768 [c739, c766, c69, c755, c749, c99, c556, c375, c36, c49, c324, c68, c81, c767, c2, c149, c577, c276, c296, c587] c768 unsat768 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c755 := derived755 a h
  have h4 : Entails.eval a c749 := derived749 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c556 := derived556 a h
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c324 := h 323 (by decide)
  have h11 : Entails.eval a c68 := h 67 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c767 := derived767 a h
  have h14 : Entails.eval a c2 := h 1 (by decide)
  have h15 : Entails.eval a c149 := h 148 (by decide)
  have h16 : Entails.eval a c577 := derived577 a h
  have h17 : Entails.eval a c276 := h 275 (by decide)
  have h18 : Entails.eval a c296 := h 295 (by decide)
  have h19 : Entails.eval a c587 := derived587 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c769 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f769 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c263, some c19, some c351, some c195, some c262, some c312, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p769 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked769 : lratChecker f769 p769 = .success := by decide +kernel
theorem unsat769 : Unsatisfiable (PosFin 57) f769 := by
  apply lratCheckerSound f769 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p769
  · intro a ha; simp [p769] at ha; subst a; trivial
  · exact checked769
theorem derived769 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c769 := by
  apply localUnsat_implies_entails f769 [c189, c263, c19, c351, c195, c262, c312] c769 unsat769 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c351 := h 350 (by decide)
  have h4 : Entails.eval a c195 := h 194 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c770 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f770 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c766, some c69, some c755, some c749, some c99, some c556, some c375, some c40, some c51, some c344, some c346, some c769, some c273, some c149, some c2, some c117, some c178, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p770 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked770 : lratChecker f770 p770 = .success := by decide +kernel
theorem unsat770 : Unsatisfiable (PosFin 57) f770 := by
  apply lratCheckerSound f770 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p770
  · intro a ha; simp [p770] at ha; subst a; trivial
  · exact checked770
theorem derived770 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c770 := by
  apply localUnsat_implies_entails f770 [c739, c766, c69, c755, c749, c99, c556, c375, c40, c51, c344, c346, c769, c273, c149, c2, c117, c178] c770 unsat770 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c755 := derived755 a h
  have h4 : Entails.eval a c749 := derived749 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c556 := derived556 a h
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c346 := h 345 (by decide)
  have h12 : Entails.eval a c769 := derived769 a h
  have h13 : Entails.eval a c273 := h 272 (by decide)
  have h14 : Entails.eval a c149 := h 148 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c771 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f771 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c766, some c556, some c768, some c596, some c88, some c755, some c749, some c99, some c691, some c770, some c304, some c296, some c34, some c350, some c349, some c268, some c192, some c352, some c29, some c208, some c252, some c412, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p771 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked771 : lratChecker f771 p771 = .success := by decide +kernel
theorem unsat771 : Unsatisfiable (PosFin 57) f771 := by
  apply lratCheckerSound f771 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p771
  · intro a ha; simp [p771] at ha; subst a; trivial
  · exact checked771
theorem derived771 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c771 := by
  apply localUnsat_implies_entails f771 [c739, c766, c556, c768, c596, c88, c755, c749, c99, c691, c770, c304, c296, c34, c350, c349, c268, c192, c352, c29, c208, c252, c412] c771 unsat771 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c556 := derived556 a h
  have h3 : Entails.eval a c768 := derived768 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c755 := derived755 a h
  have h7 : Entails.eval a c749 := derived749 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c691 := derived691 a h
  have h10 : Entails.eval a c770 := derived770 a h
  have h11 : Entails.eval a c304 := h 303 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c192 := h 191 (by decide)
  have h18 : Entails.eval a c352 := h 351 (by decide)
  have h19 : Entails.eval a c29 := h 28 (by decide)
  have h20 : Entails.eval a c208 := h 207 (by decide)
  have h21 : Entails.eval a c252 := h 251 (by decide)
  have h22 : Entails.eval a c412 := derived412 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c772 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f772 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c768, some c755, some c691, some c771, some c194, some c29, some c192, some c351, some c749, some c99, some c272, some c204, some c344, some c252, some c412, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p772 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked772 : lratChecker f772 p772 = .success := by decide +kernel
theorem unsat772 : Unsatisfiable (PosFin 57) f772 := by
  apply lratCheckerSound f772 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p772
  · intro a ha; simp [p772] at ha; subst a; trivial
  · exact checked772
theorem derived772 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c772 := by
  apply localUnsat_implies_entails f772 [c768, c755, c691, c771, c194, c29, c192, c351, c749, c99, c272, c204, c344, c252, c412] c772 unsat772 (by rfl) a
  have h0 : Entails.eval a c768 := derived768 a h
  have h1 : Entails.eval a c755 := derived755 a h
  have h2 : Entails.eval a c691 := derived691 a h
  have h3 : Entails.eval a c771 := derived771 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c749 := derived749 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c272 := h 271 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c252 := h 251 (by decide)
  have h14 : Entails.eval a c412 := derived412 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c773 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f773 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c755, some c749, some c99, some c739, some c691, some c768, some c771, some c194, some c18, some c29, some c199, some c772, some c304, some c305, some c51, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p773 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked773 : lratChecker f773 p773 = .success := by decide +kernel
theorem unsat773 : Unsatisfiable (PosFin 57) f773 := by
  apply lratCheckerSound f773 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p773
  · intro a ha; simp [p773] at ha; subst a; trivial
  · exact checked773
theorem derived773 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c773 := by
  apply localUnsat_implies_entails f773 [c755, c749, c99, c739, c691, c768, c771, c194, c18, c29, c199, c772, c304, c305, c51] c773 unsat773 (by rfl) a
  have h0 : Entails.eval a c755 := derived755 a h
  have h1 : Entails.eval a c749 := derived749 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c768 := derived768 a h
  have h6 : Entails.eval a c771 := derived771 a h
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c772 := derived772 a h
  have h12 : Entails.eval a c304 := h 303 (by decide)
  have h13 : Entails.eval a c305 := h 304 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c774 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨53, by decide⟩, true), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f774 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c88, some c336, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p774 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked774 : lratChecker f774 p774 = .success := by decide +kernel
theorem unsat774 : Unsatisfiable (PosFin 57) f774 := by
  apply lratCheckerSound f774 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p774
  · intro a ha; simp [p774] at ha; subst a; trivial
  · exact checked774
theorem derived774 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c774 := by
  apply localUnsat_implies_entails f774 [c56, c88, c336] c774 unsat774 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c775 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f775 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c739, some c766, some c69, some c755, some c749, some c99, some c691, some c556, some c375, some c773, some c37, some c63, some c344, some c774, some c596, some c49, some c304, some c272, some c195, some c346, some c19, some c189, some c273, some c149, some c2, some c117, some c178, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p775 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked775 : lratChecker f775 p775 = .success := by decide +kernel
theorem unsat775 : Unsatisfiable (PosFin 57) f775 := by
  apply lratCheckerSound f775 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p775
  · intro a ha; simp [p775] at ha; subst a; trivial
  · exact checked775
theorem derived775 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c775 := by
  apply localUnsat_implies_entails f775 [c739, c766, c69, c755, c749, c99, c691, c556, c375, c773, c37, c63, c344, c774, c596, c49, c304, c272, c195, c346, c19, c189, c273, c149, c2, c117, c178] c775 unsat775 (by rfl) a
  have h0 : Entails.eval a c739 := derived739 a h
  have h1 : Entails.eval a c766 := derived766 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c755 := derived755 a h
  have h4 : Entails.eval a c749 := derived749 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c691 := derived691 a h
  have h7 : Entails.eval a c556 := derived556 a h
  have h8 : Entails.eval a c375 := h 374 (by decide)
  have h9 : Entails.eval a c773 := derived773 a h
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c774 := derived774 a h
  have h14 : Entails.eval a c596 := derived596 a h
  have h15 : Entails.eval a c49 := h 48 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c195 := h 194 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c189 := h 188 (by decide)
  have h22 : Entails.eval a c273 := h 272 (by decide)
  have h23 : Entails.eval a c149 := h 148 (by decide)
  have h24 : Entails.eval a c2 := h 1 (by decide)
  have h25 : Entails.eval a c117 := h 116 (by decide)
  have h26 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c776 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨37, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f776 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c749, some c99, some c775, some c739, some c766, some c69, some c37, some c284, some c556, some c63, some c774, some c596, some c81, some c344, some c691, some c375, some c304, some c272, some c195, some c346, some c350, some c19, some c189, some c265, some c388, some c273, some c296, some c353, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p776 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked776 : lratChecker f776 p776 = .success := by decide +kernel
theorem unsat776 : Unsatisfiable (PosFin 57) f776 := by
  apply lratCheckerSound f776 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p776
  · intro a ha; simp [p776] at ha; subst a; trivial
  · exact checked776
theorem derived776 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c776 := by
  apply localUnsat_implies_entails f776 [c749, c99, c775, c739, c766, c69, c37, c284, c556, c63, c774, c596, c81, c344, c691, c375, c304, c272, c195, c346, c350, c19, c189, c265, c388, c273, c296, c353] c776 unsat776 (by rfl) a
  have h0 : Entails.eval a c749 := derived749 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c775 := derived775 a h
  have h3 : Entails.eval a c739 := derived739 a h
  have h4 : Entails.eval a c766 := derived766 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c284 := h 283 (by decide)
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c774 := derived774 a h
  have h11 : Entails.eval a c596 := derived596 a h
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c344 := h 343 (by decide)
  have h14 : Entails.eval a c691 := derived691 a h
  have h15 : Entails.eval a c375 := h 374 (by decide)
  have h16 : Entails.eval a c304 := h 303 (by decide)
  have h17 : Entails.eval a c272 := h 271 (by decide)
  have h18 : Entails.eval a c195 := h 194 (by decide)
  have h19 : Entails.eval a c346 := h 345 (by decide)
  have h20 : Entails.eval a c350 := h 349 (by decide)
  have h21 : Entails.eval a c19 := h 18 (by decide)
  have h22 : Entails.eval a c189 := h 188 (by decide)
  have h23 : Entails.eval a c265 := h 264 (by decide)
  have h24 : Entails.eval a c388 := derived388 a h
  have h25 : Entails.eval a c273 := h 272 (by decide)
  have h26 : Entails.eval a c296 := h 295 (by decide)
  have h27 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c777 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨48, by decide⟩, false), (⟨52, by decide⟩, false), (⟨40, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f777 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c346, some c350, some c327, some c154, some c2, some c149, some c577, some c273, some c294, some c261, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p777 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked777 : lratChecker f777 p777 = .success := by decide +kernel
theorem unsat777 : Unsatisfiable (PosFin 57) f777 := by
  apply lratCheckerSound f777 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p777
  · intro a ha; simp [p777] at ha; subst a; trivial
  · exact checked777
theorem derived777 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c777 := by
  apply localUnsat_implies_entails f777 [c69, c346, c350, c327, c154, c2, c149, c577, c273, c294, c261] c777 unsat777 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c350 := h 349 (by decide)
  have h3 : Entails.eval a c327 := h 326 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c149 := h 148 (by decide)
  have h7 : Entails.eval a c577 := derived577 a h
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c778 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f778 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c775, some c739, some c766, some c69, some c755, some c749, some c99, some c691, some c556, some c375, some c37, some c63, some c311, some c284, some c344, some c774, some c596, some c68, some c81, some c776, some c47, some c777, some c194, some c272, some c18, some c23, some c305, some c189, some c197, some c198, some c316, some c294, some c27, some c353, some c213, some c320, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p778 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked778 : lratChecker f778 p778 = .success := by decide +kernel
theorem unsat778 : Unsatisfiable (PosFin 57) f778 := by
  apply lratCheckerSound f778 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p778
  · intro a ha; simp [p778] at ha; subst a; trivial
  · exact checked778
theorem derived778 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c778 := by
  apply localUnsat_implies_entails f778 [c775, c739, c766, c69, c755, c749, c99, c691, c556, c375, c37, c63, c311, c284, c344, c774, c596, c68, c81, c776, c47, c777, c194, c272, c18, c23, c305, c189, c197, c198, c316, c294, c27, c353, c213, c320] c778 unsat778 (by rfl) a
  have h0 : Entails.eval a c775 := derived775 a h
  have h1 : Entails.eval a c739 := derived739 a h
  have h2 : Entails.eval a c766 := derived766 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c755 := derived755 a h
  have h5 : Entails.eval a c749 := derived749 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c691 := derived691 a h
  have h8 : Entails.eval a c556 := derived556 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  have h14 : Entails.eval a c344 := h 343 (by decide)
  have h15 : Entails.eval a c774 := derived774 a h
  have h16 : Entails.eval a c596 := derived596 a h
  have h17 : Entails.eval a c68 := h 67 (by decide)
  have h18 : Entails.eval a c81 := h 80 (by decide)
  have h19 : Entails.eval a c776 := derived776 a h
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c777 := derived777 a h
  have h22 : Entails.eval a c194 := h 193 (by decide)
  have h23 : Entails.eval a c272 := h 271 (by decide)
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c23 := h 22 (by decide)
  have h26 : Entails.eval a c305 := h 304 (by decide)
  have h27 : Entails.eval a c189 := h 188 (by decide)
  have h28 : Entails.eval a c197 := h 196 (by decide)
  have h29 : Entails.eval a c198 := h 197 (by decide)
  have h30 : Entails.eval a c316 := h 315 (by decide)
  have h31 : Entails.eval a c294 := h 293 (by decide)
  have h32 : Entails.eval a c27 := h 26 (by decide)
  have h33 : Entails.eval a c353 := h 352 (by decide)
  have h34 : Entails.eval a c213 := h 212 (by decide)
  have h35 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c779 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨39, by decide⟩, true), (⟨1, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f779 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c778, some c775, some c739, some c766, some c69, some c755, some c749, some c99, some c691, some c375, some c194, some c272, some c18, some c304, some c743, some c51, some c311, some c305, some c266, some c47, some c189, some c198, some c351, some c322, some c313, some c27, some c216, some c354, some c355, some c245, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p779 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked779 : lratChecker f779 p779 = .success := by decide +kernel
theorem unsat779 : Unsatisfiable (PosFin 57) f779 := by
  apply lratCheckerSound f779 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p779
  · intro a ha; simp [p779] at ha; subst a; trivial
  · exact checked779
theorem derived779 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c779 := by
  apply localUnsat_implies_entails f779 [c778, c775, c739, c766, c69, c755, c749, c99, c691, c375, c194, c272, c18, c304, c743, c51, c311, c305, c266, c47, c189, c198, c351, c322, c313, c27, c216, c354, c355, c245] c779 unsat779 (by rfl) a
  have h0 : Entails.eval a c778 := derived778 a h
  have h1 : Entails.eval a c775 := derived775 a h
  have h2 : Entails.eval a c739 := derived739 a h
  have h3 : Entails.eval a c766 := derived766 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c755 := derived755 a h
  have h6 : Entails.eval a c749 := derived749 a h
  have h7 : Entails.eval a c99 := h 98 (by decide)
  have h8 : Entails.eval a c691 := derived691 a h
  have h9 : Entails.eval a c375 := h 374 (by decide)
  have h10 : Entails.eval a c194 := h 193 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c304 := h 303 (by decide)
  have h14 : Entails.eval a c743 := derived743 a h
  have h15 : Entails.eval a c51 := h 50 (by decide)
  have h16 : Entails.eval a c311 := h 310 (by decide)
  have h17 : Entails.eval a c305 := h 304 (by decide)
  have h18 : Entails.eval a c266 := h 265 (by decide)
  have h19 : Entails.eval a c47 := h 46 (by decide)
  have h20 : Entails.eval a c189 := h 188 (by decide)
  have h21 : Entails.eval a c198 := h 197 (by decide)
  have h22 : Entails.eval a c351 := h 350 (by decide)
  have h23 : Entails.eval a c322 := h 321 (by decide)
  have h24 : Entails.eval a c313 := h 312 (by decide)
  have h25 : Entails.eval a c27 := h 26 (by decide)
  have h26 : Entails.eval a c216 := h 215 (by decide)
  have h27 : Entails.eval a c354 := h 353 (by decide)
  have h28 : Entails.eval a c355 := h 354 (by decide)
  have h29 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c780 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨34, by decide⟩, true), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, false), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, false), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f780 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c189, some c261, some c19, some c18, some c308, some c213, some c202, some c262, some c256, some c351, some c216, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p780 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked780 : lratChecker f780 p780 = .success := by decide +kernel
theorem unsat780 : Unsatisfiable (PosFin 57) f780 := by
  apply lratCheckerSound f780 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p780
  · intro a ha; simp [p780] at ha; subst a; trivial
  · exact checked780
theorem derived780 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c780 := by
  apply localUnsat_implies_entails f780 [c189, c261, c19, c18, c308, c213, c202, c262, c256, c351, c216] c780 unsat780 (by rfl) a
  have h0 : Entails.eval a c189 := h 188 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  have h9 : Entails.eval a c351 := h 350 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived780

end CochromaticTwenty.Certificates.B16_8_2
