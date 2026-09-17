import MerLeanExperiment.Certificates.B16_5_2.Steps0200_0299

/-! Generated from the actual pinned b16_5_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_5_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c653 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨6, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c634, some c100, some c104, some c636, some c652, some c13, some c165, some c641, some c39, some c71, some c211, some c221, some c30, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c611, c634, c100, c104, c636, c652, c13, c165, c641, c39, c71, c211, c221, c30] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c634 := derived634 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c636 := derived636 a h
  have h5 : Entails.eval a c652 := derived652 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c641 := derived641 a h
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c211 := h 210 (by decide)
  have h12 : Entails.eval a c221 := h 220 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c634, some c100, some c104, some c636, some c652, some c13, some c641, some c165, some c653, some c223, some c30, some c209, some c221, some c38, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c611, c634, c100, c104, c636, c652, c13, c641, c165, c653, c223, c30, c209, c221, c38] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c634 := derived634 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c636 := derived636 a h
  have h5 : Entails.eval a c652 := derived652 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c641 := derived641 a h
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c653 := derived653 a h
  have h10 : Entails.eval a c223 := h 222 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨34, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c38, some c63, some c286, some c51, some c43, some c307, some c23, some c88, some c222, some c325, some c19, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c654, c38, c63, c286, c51, c43, c307, c23, c88, c222, c325, c19] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c286 := h 285 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c222 := h 221 (by decide)
  have h10 : Entails.eval a c325 := h 324 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c43, some c307, some c302, some c88, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c51, c43, c307, c302, c88] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c307 := h 306 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c286, some c290, some c54, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c286, c290, c54] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c286 := h 285 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c657, some c654, some c655, some c656, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c657, c654, c655, c656] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c657 := derived657 a h
  have h1 : Entails.eval a c654 := derived654 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c656 := derived656 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c657, some c51, some c43, some c658, some c64, some c71, some c302, some c22, some c88, some c219, some c329, some c19, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c654, c657, c51, c43, c658, c64, c71, c302, c22, c88, c219, c329, c19] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c657 := derived657 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c658 := derived658 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c302 := h 301 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c329 := h 328 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨1, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c43, some c51, some c611, some c318, some c302, some c70, some c165, some c101, some c4, some c62, some c141, some c287, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c654, c43, c51, c611, c318, c302, c70, c165, c101, c4, c62, c141, c287] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨49, by decide⟩, true), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨1, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c290, some c43, some c51, some c611, some c287, some c62, some c101, some c638, some c70, some c209, some c211, some c229, some c236, some c19, some c329, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c654, c290, c43, c51, c611, c287, c62, c101, c638, c70, c209, c211, c229, c236, c19, c329] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c638 := derived638 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c211 := h 210 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨40, by decide⟩, false), (⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c39, some c290, some c43, some c51, some c64, some c211, some c229, some c23, some c19, some c329, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c654, c39, c290, c43, c51, c64, c211, c229, c23, c19, c329] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c638, some c641, some c4, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c638, c641, c4] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c638 := derived638 a h
  have h1 : Entails.eval a c641 := derived641 a h
  have h2 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c611, some c663, some c662, some c70, some c165, some c4, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c659, c611, c663, c662, c70, c165, c4] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c663 := derived663 a h
  have h3 : Entails.eval a c662 := derived662 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c654, some c611, some c39, some c64, some c290, some c51, some c43, some c660, some c664, some c158, some c133, some c287, some c661, some c62, some c325, some c101, some c19, some c638, some c70, some c229, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c659, c654, c611, c39, c64, c290, c51, c43, c660, c664, c158, c133, c287, c661, c62, c325, c101, c19, c638, c70, c229] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c654 := derived654 a h
  have h2 : Entails.eval a c611 := derived611 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c290 := h 289 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c660 := derived660 a h
  have h9 : Entails.eval a c664 := derived664 a h
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c287 := h 286 (by decide)
  have h13 : Entails.eval a c661 := derived661 a h
  have h14 : Entails.eval a c62 := h 61 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c19 := h 18 (by decide)
  have h18 : Entails.eval a c638 := derived638 a h
  have h19 : Entails.eval a c70 := h 69 (by decide)
  have h20 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨40, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c665, some c321, some c43, some c290, some c47, some c68, some c216, some c223, some c27, some c16, some c329, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c654, c665, c321, c43, c290, c47, c68, c216, c223, c27, c16, c329] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c321 := h 320 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c216 := h 215 (by decide)
  have h8 : Entails.eval a c223 := h 222 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c665, some c659, some c654, some c321, some c43, some c286, some c666, some c638, some c663, some c101, some c133, some c80, some c319, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c665, c659, c654, c321, c43, c286, c666, c638, c663, c101, c133, c80, c319] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c654 := derived654 a h
  have h3 : Entails.eval a c321 := h 320 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c286 := h 285 (by decide)
  have h6 : Entails.eval a c666 := derived666 a h
  have h7 : Entails.eval a c638 := derived638 a h
  have h8 : Entails.eval a c663 := derived663 a h
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c141, some c133, some c68, some c80, some c303, some c98, some c28, some c325, some c220, some c107, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c141, c133, c68, c80, c303, c98, c28, c325, c220, c107] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c133 := h 132 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c220 := h 219 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c659, some c611, some c667, some c70, some c165, some c4, some c101, some c654, some c286, some c290, some c133, some c141, some c668, some c637, some c27, some c98, some c219, some c303, some c107, some c69, some c326, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c659, c611, c667, c70, c165, c4, c101, c654, c286, c290, c133, c141, c668, c637, c27, c98, c219, c303, c107, c69, c326] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c659 := derived659 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c654 := derived654 a h
  have h8 : Entails.eval a c286 := h 285 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c668 := derived668 a h
  have h13 : Entails.eval a c637 := derived637 a h
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c219 := h 218 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c69 := h 68 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c611, some c659, some c667, some c70, some c165, some c101, some c4, some c669, some c660, some c62, some c133, some c287, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c654, c611, c659, c667, c70, c165, c101, c4, c669, c660, c62, c133, c287] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c667 := derived667 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c669 := derived669 a h
  have h9 : Entails.eval a c660 := derived660 a h
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c287 := h 286 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨33, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c158, some c43, some c51, some c166, some c307, some c116, some c187, some c222, some c325, some c19, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c158, c43, c51, c166, c307, c116, c187, c222, c325, c19] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c158 := h 157 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c307 := h 306 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c222 := h 221 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨41, by decide⟩, false), (⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c287, some c62, some c43, some c51, some c670, some c611, some c101, some c7, some c641, some c165, some c209, some c229, some c22, some c19, some c325, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c654, c287, c62, c43, c51, c670, c611, c101, c7, c641, c165, c209, c229, c22, c19, c325] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c670 := derived670 a h
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c641 := derived641 a h
  have h10 : Entails.eval a c165 := h 164 (by decide)
  have h11 : Entails.eval a c209 := h 208 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c43, some c51, some c611, some c158, some c671, some c672, some c638, some c70, some c209, some c229, some c115, some c19, some c325, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c654, c43, c51, c611, c158, c671, c672, c638, c70, c209, c229, c115, c19, c325] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c672 := derived672 a h
  have h7 : Entails.eval a c638 := derived638 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false), (⟨33, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c325, some c63, some c99, some c3, some c640, some c147, some c346, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c325, c63, c99, c3, c640, c147, c346] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c325 := h 324 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c640 := derived640 a h
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨33, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c673, some c654, some c287, some c62, some c43, some c51, some c611, some c638, some c70, some c209, some c229, some c19, some c674, some c22, some c99, some c3, some c640, some c86, some c139, some c147, some c336, some c230, some c113, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c673, c654, c287, c62, c43, c51, c611, c638, c70, c209, c229, c19, c674, c22, c99, c3, c640, c86, c139, c147, c336, c230, c113] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c673 := derived673 a h
  have h1 : Entails.eval a c654 := derived654 a h
  have h2 : Entails.eval a c287 := h 286 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c638 := derived638 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c209 := h 208 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c674 := derived674 a h
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c640 := derived640 a h
  have h17 : Entails.eval a c86 := h 85 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c336 := h 335 (by decide)
  have h21 : Entails.eval a c230 := h 229 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c14, some c157, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c199, c14, c157] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c287, some c62, some c43, some c51, some c611, some c673, some c675, some c101, some c63, some c676, some c641, some c165, some c209, some c229, some c22, some c19, some c325, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c654, c287, c62, c43, c51, c611, c673, c675, c101, c63, c676, c641, c165, c209, c229, c22, c19, c325] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c287 := h 286 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c673 := derived673 a h
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c676 := derived676 a h
  have h11 : Entails.eval a c641 := derived641 a h
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c229 := h 228 (by decide)
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c19 := h 18 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c43, some c51, some c670, some c611, some c287, some c62, some c677, some c318, some c660, some c302, some c70, some c165, some c22, some c7, some c676, some c219, some c187, some c19, some c329, some c307, some c159, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c654, c43, c51, c670, c611, c287, c62, c677, c318, c660, c302, c70, c165, c22, c7, c676, c219, c187, c19, c329, c307, c159] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c670 := derived670 a h
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c677 := derived677 a h
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c660 := derived660 a h
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c165 := h 164 (by decide)
  have h13 : Entails.eval a c22 := h 21 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c676 := derived676 a h
  have h16 : Entails.eval a c219 := h 218 (by decide)
  have h17 : Entails.eval a c187 := h 186 (by decide)
  have h18 : Entails.eval a c19 := h 18 (by decide)
  have h19 : Entails.eval a c329 := h 328 (by decide)
  have h20 : Entails.eval a c307 := h 306 (by decide)
  have h21 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c678, some c654, some c43, some c51, some c660, some c302, some c46, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c678, c654, c43, c51, c660, c302, c46] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c678 := derived678 a h
  have h1 : Entails.eval a c654 := derived654 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c660 := derived660 a h
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c678, some c679, some c133, some c38, some c663, some c654, some c43, some c611, some c101, some c4, some c62, some c165, some c217, some c229, some c37, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c678, c679, c133, c38, c663, c654, c43, c611, c101, c4, c62, c165, c217, c229, c37] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c678 := derived678 a h
  have h1 : Entails.eval a c679 := derived679 a h
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c663 := derived663 a h
  have h5 : Entails.eval a c654 := derived654 a h
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c611 := derived611 a h
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c165 := h 164 (by decide)
  have h12 : Entails.eval a c217 := h 216 (by decide)
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c678, some c679, some c133, some c38, some c663, some c654, some c43, some c611, some c680, some c70, some c229, some c62, some c37, some c217, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c678, c679, c133, c38, c663, c654, c43, c611, c680, c70, c229, c62, c37, c217] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c678 := derived678 a h
  have h1 : Entails.eval a c679 := derived679 a h
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c663 := derived663 a h
  have h5 : Entails.eval a c654 := derived654 a h
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c611 := derived611 a h
  have h8 : Entails.eval a c680 := derived680 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c680, some c678, some c679, some c38, some c681, some c99, some c86, some c654, some c60, some c133, some c3, some c663, some c217, some c273, some c113, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c611, c680, c678, c679, c38, c681, c99, c86, c654, c60, c133, c3, c663, c217, c273, c113] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c680 := derived680 a h
  have h2 : Entails.eval a c678 := derived678 a h
  have h3 : Entails.eval a c679 := derived679 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c681 := derived681 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c654 := derived654 a h
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c663 := derived663 a h
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c273 := h 272 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c678, some c679, some c38, some c133, some c663, some c680, some c70, some c681, some c99, some c3, some c640, some c86, some c682, some c139, some c147, some c230, some c336, some c113, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c611, c678, c679, c38, c133, c663, c680, c70, c681, c99, c3, c640, c86, c682, c139, c147, c230, c336, c113] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c678 := derived678 a h
  have h2 : Entails.eval a c679 := derived679 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c663 := derived663 a h
  have h6 : Entails.eval a c680 := derived680 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c681 := derived681 a h
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c640 := derived640 a h
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c682 := derived682 a h
  have h14 : Entails.eval a c139 := h 138 (by decide)
  have h15 : Entails.eval a c147 := h 146 (by decide)
  have h16 : Entails.eval a c230 := h 229 (by decide)
  have h17 : Entails.eval a c336 := h 335 (by decide)
  have h18 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c19, some c27, some c683, some c290, some c611, some c152, some c132, some c203, some c202, some c183, some c643, some c335, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c654, c19, c27, c683, c290, c611, c152, c132, c203, c202, c183, c643, c335] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c183 := h 182 (by decide)
  have h11 : Entails.eval a c643 := derived643 a h
  have h12 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨40, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨24, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c38, some c325, some c221, some c15, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c46, c38, c325, c221, c15] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c654, some c683, some c216, some c19, some c27, some c286, some c611, some c685, some c99, some c101, some c3, some c640, some c86, some c141, some c613, some c324, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c654, c683, c216, c19, c27, c286, c611, c685, c99, c101, c3, c640, c86, c141, c613, c324] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c654 := derived654 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c216 := h 215 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c286 := h 285 (by decide)
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c685 := derived685 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c640 := derived640 a h
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c141 := h 140 (by decide)
  have h14 : Entails.eval a c613 := derived613 a h
  have h15 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c216, some c654, some c611, some c37, some c684, some c686, some c70, some c165, some c14, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c683, c216, c654, c611, c37, c684, c686, c70, c165, c14] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c654 := derived654 a h
  have h3 : Entails.eval a c611 := derived611 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c684 := derived684 a h
  have h6 : Entails.eval a c686 := derived686 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c290, some c670, some c14, some c7, some c152, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c683, c290, c670, c14, c7, c152] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c670 := derived670 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c687, some c611, some c688, some c70, some c686, some c230, some c139, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c687, c611, c688, c70, c686, c230, c139] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c687 := derived687 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c688 := derived688 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c686 := derived686 a h
  have h5 : Entails.eval a c230 := h 229 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c687, some c683, some c290, some c286, some c670, some c611, some c689, some c44, some c230, some c70, some c7, some c149, some c152, some c200, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c687, c683, c290, c286, c670, c611, c689, c44, c230, c70, c7, c149, c152, c200] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c687 := derived687 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c286 := h 285 (by decide)
  have h4 : Entails.eval a c670 := derived670 a h
  have h5 : Entails.eval a c611 := derived611 a h
  have h6 : Entails.eval a c689 := derived689 a h
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c230 := h 229 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c7 := h 6 (by decide)
  have h11 : Entails.eval a c149 := h 148 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c687, some c690, some c165, some c230, some c44, some c139, some c686, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c611, c687, c690, c165, c230, c44, c139, c686] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c687 := derived687 a h
  have h2 : Entails.eval a c690 := derived690 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c686 := derived686 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c290, some c286, some c670, some c691, some c638, some c641, some c7, some c149, some c152, some c200, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c683, c290, c286, c670, c691, c638, c641, c7, c149, c152, c200] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  have h3 : Entails.eval a c670 := derived670 a h
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c638 := derived638 a h
  have h6 : Entails.eval a c641 := derived641 a h
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c692, some c683, some c290, some c286, some c670, some c654, some c611, some c200, some c149, some c7, some c638, some c70, some c216, some c217, some c686, some c37, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c692, c683, c290, c286, c670, c654, c611, c200, c149, c7, c638, c70, c216, c217, c686, c37] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c692 := derived692 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c286 := h 285 (by decide)
  have h4 : Entails.eval a c670 := derived670 a h
  have h5 : Entails.eval a c654 := derived654 a h
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c7 := h 6 (by decide)
  have h10 : Entails.eval a c638 := derived638 a h
  have h11 : Entails.eval a c70 := h 69 (by decide)
  have h12 : Entails.eval a c216 := h 215 (by decide)
  have h13 : Entails.eval a c217 := h 216 (by decide)
  have h14 : Entails.eval a c686 := derived686 a h
  have h15 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c290, some c286, some c199, some c203, some c149, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c683, c290, c286, c199, c203, c149] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c290, some c134, some c286, some c149, some c694, some c693, some c132, some c121, some c127, some c216, some c222, some c663, some c175, some c46, some c38, some c303, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c683, c290, c134, c286, c149, c694, c693, c132, c121, c127, c216, c222, c663, c175, c46, c38, c303] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c286 := h 285 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c694 := derived694 a h
  have h6 : Entails.eval a c693 := derived693 a h
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c663 := derived663 a h
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c46 := h 45 (by decide)
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c683, some c286, some c290, some c149, some c692, some c695, some c217, some c663, some c38, some c46, some c142, some c134, some c694, some c693, some c654, some c501, some c303, some c15, some c197, some c325, some c307, some c68, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c683, c286, c290, c149, c692, c695, c217, c663, c38, c46, c142, c134, c694, c693, c654, c501, c303, c15, c197, c325, c307, c68] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c683 := derived683 a h
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c692 := derived692 a h
  have h5 : Entails.eval a c695 := derived695 a h
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c663 := derived663 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c134 := h 133 (by decide)
  have h12 : Entails.eval a c694 := derived694 a h
  have h13 : Entails.eval a c693 := derived693 a h
  have h14 : Entails.eval a c654 := derived654 a h
  have h15 : Entails.eval a c501 := derived501 a h
  have h16 : Entails.eval a c303 := h 302 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c325 := h 324 (by decide)
  have h20 : Entails.eval a c307 := h 306 (by decide)
  have h21 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c694, some c693, some c692, some c683, some c290, some c286, some c654, some c149, some c695, some c217, some c663, some c46, some c38, some c696, some c164, some c175, some c302, some c197, some c326, some c27, some c15, some c219, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c694, c693, c692, c683, c290, c286, c654, c149, c695, c217, c663, c46, c38, c696, c164, c175, c302, c197, c326, c27, c15, c219] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c694 := derived694 a h
  have h1 : Entails.eval a c693 := derived693 a h
  have h2 : Entails.eval a c692 := derived692 a h
  have h3 : Entails.eval a c683 := derived683 a h
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c286 := h 285 (by decide)
  have h6 : Entails.eval a c654 := derived654 a h
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c695 := derived695 a h
  have h9 : Entails.eval a c217 := h 216 (by decide)
  have h10 : Entails.eval a c663 := derived663 a h
  have h11 : Entails.eval a c46 := h 45 (by decide)
  have h12 : Entails.eval a c38 := h 37 (by decide)
  have h13 : Entails.eval a c696 := derived696 a h
  have h14 : Entails.eval a c164 := h 163 (by decide)
  have h15 : Entails.eval a c175 := h 174 (by decide)
  have h16 : Entails.eval a c302 := h 301 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c27 := h 26 (by decide)
  have h20 : Entails.eval a c15 := h 14 (by decide)
  have h21 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c692, some c683, some c670, some c693, some c694, some c697, some c7, some c638, some c216, some c217, some c132, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c692, c683, c670, c693, c694, c697, c7, c638, c216, c217, c132] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c692 := derived692 a h
  have h1 : Entails.eval a c683 := derived683 a h
  have h2 : Entails.eval a c670 := derived670 a h
  have h3 : Entails.eval a c693 := derived693 a h
  have h4 : Entails.eval a c694 := derived694 a h
  have h5 : Entails.eval a c697 := derived697 a h
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c638 := derived638 a h
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c217 := h 216 (by decide)
  have h10 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c654, some c683, some c286, some c692, some c698, some c641, some c165, some c216, some c217, some c27, some c19, some c37, some c685, some c686, some c101, some c99, some c113, some c121, some c640, some c86, some c336, some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c611, c654, c683, c286, c692, c698, c641, c165, c216, c217, c27, c19, c37, c685, c686, c101, c99, c113, c121, c640, c86, c336] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c654 := derived654 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c286 := h 285 (by decide)
  have h4 : Entails.eval a c692 := derived692 a h
  have h5 : Entails.eval a c698 := derived698 a h
  have h6 : Entails.eval a c641 := derived641 a h
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c217 := h 216 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c685 := derived685 a h
  have h14 : Entails.eval a c686 := derived686 a h
  have h15 : Entails.eval a c101 := h 100 (by decide)
  have h16 : Entails.eval a c99 := h 98 (by decide)
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c121 := h 120 (by decide)
  have h19 : Entails.eval a c640 := derived640 a h
  have h20 : Entails.eval a c86 := h 85 (by decide)
  have h21 : Entails.eval a c336 := h 335 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c639, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c699, c639] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c639 := derived639 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c642, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c699, c642] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c642 := derived642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨31, by decide⟩, false), (⟨9, by decide⟩, true), (⟨47, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c46, some c187, some c262, some c329, some c176, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c46, c187, c262, c329, c176] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c46 := h 45 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c262 := h 261 (by decide)
  have h3 : Entails.eval a c329 := h 328 (by decide)
  have h4 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨31, by decide⟩, false), (⟨14, by decide⟩, false), (⟨47, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c199, some c511, some c13, some c27, some c19, some c37, some c101, some c702, some c325, some c302, some c176, some c329, some c142, some c43, some c266, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c701, c700, c199, c511, c13, c27, c19, c37, c101, c702, c325, c302, c176, c329, c142, c43, c266] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c511 := derived511 a h
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c702 := derived702 a h
  have h10 : Entails.eval a c325 := h 324 (by decide)
  have h11 : Entails.eval a c302 := h 301 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c142 := h 141 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨31, by decide⟩, false), (⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c699, some c127, some c113, some c703, some c251, some c199, some c511, some c13, some c121, some c303, some c346, some c326, some c169, some c646, some c649, some c107, some c222, some c206, some c43, some c149, some c210, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c700, c701, c699, c127, c113, c703, c251, c199, c511, c13, c121, c303, c346, c326, c169, c646, c649, c107, c222, c206, c43, c149, c210] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c699 := derived699 a h
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c703 := derived703 a h
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c511 := derived511 a h
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c346 := h 345 (by decide)
  have h13 : Entails.eval a c326 := h 325 (by decide)
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c646 := derived646 a h
  have h16 : Entails.eval a c649 := derived649 a h
  have h17 : Entails.eval a c107 := h 106 (by decide)
  have h18 : Entails.eval a c222 := h 221 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c149 := h 148 (by decide)
  have h22 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c13, some c199, some c127, some c113, some c703, some c251, some c250, some c645, some c704, some c187, some c350, some c115, some c141, some c462, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c700, c701, c13, c199, c127, c113, c703, c251, c250, c645, c704, c187, c350, c115, c141, c462] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c703 := derived703 a h
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c250 := h 249 (by decide)
  have h9 : Entails.eval a c645 := derived645 a h
  have h10 : Entails.eval a c704 := derived704 a h
  have h11 : Entails.eval a c187 := h 186 (by decide)
  have h12 : Entails.eval a c350 := h 349 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c462 := derived462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c251, some c250, some c210, some c645, some c51, some c43, some c671, some c350, some c302, some c187, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c251, c250, c210, c645, c51, c43, c671, c350, c302, c187] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c251 := h 250 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c671 := derived671 a h
  have h7 : Entails.eval a c350 := h 349 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨46, by decide⟩, false), (⟨54, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c350, some c329, some c648, some c159, some c289, some c307, some c43, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c699, c350, c329, c648, c159, c289, c307, c43] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c648 := derived648 a h
  have h4 : Entails.eval a c159 := h 158 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c307 := h 306 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c127, some c121, some c113, some c199, some c13, some c705, some c152, some c139, some c706, some c27, some c19, some c37, some c101, some c707, some c187, some c303, some c326, some c63, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c701, c700, c127, c121, c113, c199, c13, c705, c152, c139, c706, c27, c19, c37, c101, c707, c187, c303, c326, c63] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c705 := derived705 a h
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c706 := derived706 a h
  have h11 : Entails.eval a c27 := h 26 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c101 := h 100 (by decide)
  have h15 : Entails.eval a c707 := derived707 a h
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c303 := h 302 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c708, some c132, some c127, some c152, some c157, some c210, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c708, c132, c127, c152, c157, c210] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c708 := derived708 a h
  have h1 : Entails.eval a c132 := h 131 (by decide)
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨39, by decide⟩, false), (⟨34, by decide⟩, true), (⟨55, by decide⟩, false), (⟨47, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c303, some c326, some c166, some c63, some c4, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c701, c700, c303, c326, c166, c63, c4] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c303 := h 302 (by decide)
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c127, some c708, some c132, some c251, some c250, some c645, some c121, some c113, some c138, some c146, some c222, some c350, some c169, some c710, some c187, some c4, some c46, some c22, some c399, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c701, c700, c127, c708, c132, c251, c250, c645, c121, c113, c138, c146, c222, c350, c169, c710, c187, c4, c46, c22, c399] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c127 := h 126 (by decide)
  have h3 : Entails.eval a c708 := derived708 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c250 := h 249 (by decide)
  have h7 : Entails.eval a c645 := derived645 a h
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c350 := h 349 (by decide)
  have h14 : Entails.eval a c169 := h 168 (by decide)
  have h15 : Entails.eval a c710 := derived710 a h
  have h16 : Entails.eval a c187 := h 186 (by decide)
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c46 := h 45 (by decide)
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c399 := derived399 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c700, some c701, some c127, some c708, some c132, some c251, some c250, some c645, some c129, some c709, some c711, some c210, some c355, some c350, some c349, some c192, some c647, some c204, some c292, some c151, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c699, c700, c701, c127, c708, c132, c251, c250, c645, c129, c709, c711, c210, c355, c350, c349, c192, c647, c204, c292, c151] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c708 := derived708 a h
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c645 := derived645 a h
  have h9 : Entails.eval a c129 := h 128 (by decide)
  have h10 : Entails.eval a c709 := derived709 a h
  have h11 : Entails.eval a c711 := derived711 a h
  have h12 : Entails.eval a c210 := h 209 (by decide)
  have h13 : Entails.eval a c355 := derived355 a h
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c192 := h 191 (by decide)
  have h17 : Entails.eval a c647 := derived647 a h
  have h18 : Entails.eval a c204 := h 203 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨52, by decide⟩, false), (⟨24, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c699, some c712, some c355, some c152, some c349, some c644, some c647, some c212, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c701, c700, c699, c712, c355, c152, c349, c644, c647, c212] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c699 := derived699 a h
  have h3 : Entails.eval a c712 := derived712 a h
  have h4 : Entails.eval a c355 := derived355 a h
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c644 := derived644 a h
  have h8 : Entails.eval a c647 := derived647 a h
  have h9 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨42, by decide⟩, false), (⟨36, by decide⟩, true), (⟨31, by decide⟩, false), (⟨14, by decide⟩, true), (⟨30, by decide⟩, true), (⟨26, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c288, some c212, some c292, some c264, some c136, some c155, some c109, some c204, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c288, c212, c292, c264, c136, c155, c109, c204] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c288 := h 287 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c292 := h 291 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c155 := h 154 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c251, some c250, some c645, some c713, some c210, some c712, some c157, some c138, some c146, some c222, some c350, some c313, some c159, some c191, some c714, some c647, some c352, some c646, some c649, some c215, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c699, c251, c250, c645, c713, c210, c712, c157, c138, c146, c222, c350, c313, c159, c191, c714, c647, c352, c646, c649, c215] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c251 := h 250 (by decide)
  have h2 : Entails.eval a c250 := h 249 (by decide)
  have h3 : Entails.eval a c645 := derived645 a h
  have h4 : Entails.eval a c713 := derived713 a h
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c712 := derived712 a h
  have h7 : Entails.eval a c157 := h 156 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  have h10 : Entails.eval a c222 := h 221 (by decide)
  have h11 : Entails.eval a c350 := h 349 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  have h14 : Entails.eval a c191 := h 190 (by decide)
  have h15 : Entails.eval a c714 := derived714 a h
  have h16 : Entails.eval a c647 := derived647 a h
  have h17 : Entails.eval a c352 := h 351 (by decide)
  have h18 : Entails.eval a c646 := derived646 a h
  have h19 : Entails.eval a c649 := derived649 a h
  have h20 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c251, some c250, some c645, some c713, some c715, some c199, some c13, some c706, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c701, c700, c251, c250, c645, c713, c715, c199, c13, c706] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c251 := h 250 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c713 := derived713 a h
  have h6 : Entails.eval a c715 := derived715 a h
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c706 := derived706 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨43, by decide⟩, true), (⟨28, by decide⟩, true), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c253, some c212, some c126, some c139, some c154, some c226, some c204, some c160, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c712, c253, c212, c126, c139, c154, c226, c204, c160] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c253 := h 252 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨26, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c701, some c716, some c116, some c108, some c350, some c349, some c647, some c288, some c264, some c717, some c644, some c247, some c123, some c232, some c237, some c199, some c146, some c197, some c266, some c326, some c186, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c699, c701, c716, c116, c108, c350, c349, c647, c288, c264, c717, c644, c247, c123, c232, c237, c199, c146, c197, c266, c326, c186] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c108 := h 107 (by decide)
  have h5 : Entails.eval a c350 := h 349 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c647 := derived647 a h
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c717 := derived717 a h
  have h11 : Entails.eval a c644 := derived644 a h
  have h12 : Entails.eval a c247 := h 246 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c232 := h 231 (by decide)
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c266 := h 265 (by decide)
  have h20 : Entails.eval a c326 := h 325 (by decide)
  have h21 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨30, by decide⟩, true), (⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c116, some c108, some c712, some c123, some c199, some c4, some c146, some c157, some c138, some c515, some c15, some c329, some c302, some c186, some c38, some c262, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c701, c700, c116, c108, c712, c123, c199, c4, c146, c157, c138, c515, c15, c329, c302, c186, c38, c262] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c515 := derived515 a h
  have h12 : Entails.eval a c15 := h 14 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c302 := h 301 (by decide)
  have h15 : Entails.eval a c186 := h 185 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  have h17 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c701, some c716, some c712, some c718, some c648, some c289, some c288, some c647, some c719, some c247, some c246, some c646, some c126, some c352, some c544, some c193, some c204, some c153, some c150, some c199, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c699, c701, c716, c712, c718, c648, c289, c288, c647, c719, c247, c246, c646, c126, c352, c544, c193, c204, c153, c150, c199] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c716 := derived716 a h
  have h3 : Entails.eval a c712 := derived712 a h
  have h4 : Entails.eval a c718 := derived718 a h
  have h5 : Entails.eval a c648 := derived648 a h
  have h6 : Entails.eval a c289 := h 288 (by decide)
  have h7 : Entails.eval a c288 := h 287 (by decide)
  have h8 : Entails.eval a c647 := derived647 a h
  have h9 : Entails.eval a c719 := derived719 a h
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c246 := h 245 (by decide)
  have h12 : Entails.eval a c646 := derived646 a h
  have h13 : Entails.eval a c126 := h 125 (by decide)
  have h14 : Entails.eval a c352 := h 351 (by decide)
  have h15 : Entails.eval a c544 := derived544 a h
  have h16 : Entails.eval a c193 := h 192 (by decide)
  have h17 : Entails.eval a c204 := h 203 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c150 := h 149 (by decide)
  have h20 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c720, some c152, some c134, some c716, some c116, some c712, some c719, some c208, some c149, some c199, some c146, some c138, some c307, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c701, c720, c152, c134, c716, c116, c712, c719, c208, c149, c199, c146, c138, c307] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c720 := derived720 a h
  have h2 : Entails.eval a c152 := h 151 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c716 := derived716 a h
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c712 := derived712 a h
  have h7 : Entails.eval a c719 := derived719 a h
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c149 := h 148 (by decide)
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c713, some c645, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c713, c645] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c713 := derived713 a h
  have h1 : Entails.eval a c645 := derived645 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, true), (⟨31, by decide⟩, false), (⟨34, by decide⟩, false), (⟨50, by decide⟩, false), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c32, some c30, some c102, some c31, some c212, some c647, some c40, some c305, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c699, c32, c30, c102, c31, c212, c647, c40, c305] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c647 := derived647 a h
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c720, some c152, some c134, some c716, some c116, some c712, some c722, some c247, some c723, some c123, some c4, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c701, c700, c720, c152, c134, c716, c116, c712, c722, c247, c723, c123, c4] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c720 := derived720 a h
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c716 := derived716 a h
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c712 := derived712 a h
  have h8 : Entails.eval a c722 := derived722 a h
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c723 := derived723 a h
  have h11 : Entails.eval a c123 := h 122 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c699, some c701, some c712, some c716, some c116, some c720, some c134, some c721, some c724, some c214, some c648, some c713, some c306, some c247, some c257, some c123, some c229, some c230, some c199, some c175, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c699, c701, c712, c716, c116, c720, c134, c721, c724, c214, c648, c713, c306, c247, c257, c123, c229, c230, c199, c175] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c699 := derived699 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c716 := derived716 a h
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c720 := derived720 a h
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c721 := derived721 a h
  have h8 : Entails.eval a c724 := derived724 a h
  have h9 : Entails.eval a c214 := h 213 (by decide)
  have h10 : Entails.eval a c648 := derived648 a h
  have h11 : Entails.eval a c713 := derived713 a h
  have h12 : Entails.eval a c306 := h 305 (by decide)
  have h13 : Entails.eval a c247 := h 246 (by decide)
  have h14 : Entails.eval a c257 := h 256 (by decide)
  have h15 : Entails.eval a c123 := h 122 (by decide)
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c230 := h 229 (by decide)
  have h18 : Entails.eval a c199 := h 198 (by decide)
  have h19 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c27, some c120, some c13, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c700, c701, c27, c120, c13] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c727 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨31, by decide⟩, false), (⟨26, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f727 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c726, some c199, some c13, some c149, some c500, some c19, some c208, some c325, some c107, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p727 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked727 : lratChecker f727 p727 = .success := by decide +kernel
theorem unsat727 : Unsatisfiable (PosFin 57) f727 := by
  apply lratCheckerSound f727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p727
  · intro a ha; simp [p727] at ha; subst a; trivial
  · exact checked727
theorem derived727 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c727 := by
  apply localUnsat_implies_entails f727 [c701, c700, c726, c199, c13, c149, c500, c19, c208, c325, c107] c727 unsat727 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c726 := derived726 a h
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c500 := derived500 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c728 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨42, by decide⟩, true), (⟨46, by decide⟩, false), (⟨30, by decide⟩, false), (⟨26, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f728 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c149, some c176, some c261, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p728 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked728 : lratChecker f728 p728 = .success := by decide +kernel
theorem unsat728 : Unsatisfiable (PosFin 57) f728 := by
  apply lratCheckerSound f728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p728
  · intro a ha; simp [p728] at ha; subst a; trivial
  · exact checked728
theorem derived728 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c728 := by
  apply localUnsat_implies_entails f728 [c149, c176, c261] c728 unsat728 (by rfl) a
  have h0 : Entails.eval a c149 := h 148 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c729 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f729 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c725, some c726, some c712, some c355, some c134, some c152, some c307, some c727, some c138, some c112, some c635, some c175, some c728, some c4, some c515, some c325, some c501, some c15, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p729 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked729 : lratChecker f729 p729 = .success := by decide +kernel
theorem unsat729 : Unsatisfiable (PosFin 57) f729 := by
  apply lratCheckerSound f729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p729
  · intro a ha; simp [p729] at ha; subst a; trivial
  · exact checked729
theorem derived729 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c729 := by
  apply localUnsat_implies_entails f729 [c701, c700, c725, c726, c712, c355, c134, c152, c307, c727, c138, c112, c635, c175, c728, c4, c515, c325, c501, c15] c729 unsat729 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c725 := derived725 a h
  have h3 : Entails.eval a c726 := derived726 a h
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c355 := derived355 a h
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c727 := derived727 a h
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c635 := derived635 a h
  have h13 : Entails.eval a c175 := h 174 (by decide)
  have h14 : Entails.eval a c728 := derived728 a h
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c515 := derived515 a h
  have h17 : Entails.eval a c325 := h 324 (by decide)
  have h18 : Entails.eval a c501 := derived501 a h
  have h19 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c730 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f730 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c725, some c726, some c712, some c63, some c15, some c399, some c220, some c46, some c175, some c302, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p730 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked730 : lratChecker f730 p730 = .success := by decide +kernel
theorem unsat730 : Unsatisfiable (PosFin 57) f730 := by
  apply lratCheckerSound f730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p730
  · intro a ha; simp [p730] at ha; subst a; trivial
  · exact checked730
theorem derived730 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c730 := by
  apply localUnsat_implies_entails f730 [c725, c726, c712, c63, c15, c399, c220, c46, c175, c302] c730 unsat730 (by rfl) a
  have h0 : Entails.eval a c725 := derived725 a h
  have h1 : Entails.eval a c726 := derived726 a h
  have h2 : Entails.eval a c712 := derived712 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c399 := derived399 a h
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c731 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f731 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c725, some c112, some c726, some c730, some c325, some c22, some c46, some c399, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p731 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked731 : lratChecker f731 p731 = .success := by decide +kernel
theorem unsat731 : Unsatisfiable (PosFin 57) f731 := by
  apply lratCheckerSound f731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p731
  · intro a ha; simp [p731] at ha; subst a; trivial
  · exact checked731
theorem derived731 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c731 := by
  apply localUnsat_implies_entails f731 [c725, c112, c726, c730, c325, c22, c46, c399] c731 unsat731 (by rfl) a
  have h0 : Entails.eval a c725 := derived725 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c726 := derived726 a h
  have h3 : Entails.eval a c730 := derived730 a h
  have h4 : Entails.eval a c325 := h 324 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c399 := derived399 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c732 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f732 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c729, some c725, some c726, some c112, some c731, some c100, some c4, some c707, some c187, some c191, some c325, some c158, some c303, some c302, some c175, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p732 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked732 : lratChecker f732 p732 = .success := by decide +kernel
theorem unsat732 : Unsatisfiable (PosFin 57) f732 := by
  apply lratCheckerSound f732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p732
  · intro a ha; simp [p732] at ha; subst a; trivial
  · exact checked732
theorem derived732 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c732 := by
  apply localUnsat_implies_entails f732 [c701, c700, c729, c725, c726, c112, c731, c100, c4, c707, c187, c191, c325, c158, c303, c302, c175] c732 unsat732 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c729 := derived729 a h
  have h3 : Entails.eval a c725 := derived725 a h
  have h4 : Entails.eval a c726 := derived726 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c731 := derived731 a h
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c707 := derived707 a h
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c325 := h 324 (by decide)
  have h13 : Entails.eval a c158 := h 157 (by decide)
  have h14 : Entails.eval a c303 := h 302 (by decide)
  have h15 : Entails.eval a c302 := h 301 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c733 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f733 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c725, some c726, some c729, some c732, some c199, some c13, some c19, some c707, some c187, some c325, some c158, some c176, some c302, some c266, some c43, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p733 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked733 : lratChecker f733 p733 = .success := by decide +kernel
theorem unsat733 : Unsatisfiable (PosFin 57) f733 := by
  apply lratCheckerSound f733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p733
  · intro a ha; simp [p733] at ha; subst a; trivial
  · exact checked733
theorem derived733 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c733 := by
  apply localUnsat_implies_entails f733 [c700, c701, c725, c726, c729, c732, c199, c13, c19, c707, c187, c325, c158, c176, c302, c266, c43] c733 unsat733 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c725 := derived725 a h
  have h3 : Entails.eval a c726 := derived726 a h
  have h4 : Entails.eval a c729 := derived729 a h
  have h5 : Entails.eval a c732 := derived732 a h
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c707 := derived707 a h
  have h10 : Entails.eval a c187 := h 186 (by decide)
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c176 := h 175 (by decide)
  have h14 : Entails.eval a c302 := h 301 (by decide)
  have h15 : Entails.eval a c266 := h 265 (by decide)
  have h16 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c734 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨54, by decide⟩, false), (⟨17, by decide⟩, false), (⟨33, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f734 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c733, some c203, some c302, some c175, some c220, some c303, some c121, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p734 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked734 : lratChecker f734 p734 = .success := by decide +kernel
theorem unsat734 : Unsatisfiable (PosFin 57) f734 := by
  apply lratCheckerSound f734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p734
  · intro a ha; simp [p734] at ha; subst a; trivial
  · exact checked734
theorem derived734 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c734 := by
  apply localUnsat_implies_entails f734 [c701, c733, c203, c302, c175, c220, c303, c121] c734 unsat734 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c733 := derived733 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c220 := h 219 (by decide)
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c735 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨25, by decide⟩, false), (⟨17, by decide⟩, false), (⟨33, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f735 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c733, some c203, some c399, some c101, some c100, some c138, some c175, some c207, some c220, some c37, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p735 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked735 : lratChecker f735 p735 = .success := by decide +kernel
theorem unsat735 : Unsatisfiable (PosFin 57) f735 := by
  apply lratCheckerSound f735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p735
  · intro a ha; simp [p735] at ha; subst a; trivial
  · exact checked735
theorem derived735 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c735 := by
  apply localUnsat_implies_entails f735 [c701, c700, c733, c203, c399, c101, c100, c138, c175, c207, c220, c37] c735 unsat735 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c399 := derived399 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c175 := h 174 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c736 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨41, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f736 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c107, some c158, some c733, some c203, some c141, some c399, some c100, some c101, some c735, some c219, some c37, some c220, some c500, some c139, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p736 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked736 : lratChecker f736 p736 = .success := by decide +kernel
theorem unsat736 : Unsatisfiable (PosFin 57) f736 := by
  apply lratCheckerSound f736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p736
  · intro a ha; simp [p736] at ha; subst a; trivial
  · exact checked736
theorem derived736 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c736 := by
  apply localUnsat_implies_entails f736 [c701, c700, c107, c158, c733, c203, c141, c399, c100, c101, c735, c219, c37, c220, c500, c139] c736 unsat736 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c733 := derived733 a h
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c399 := derived399 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c735 := derived735 a h
  have h11 : Entails.eval a c219 := h 218 (by decide)
  have h12 : Entails.eval a c37 := h 36 (by decide)
  have h13 : Entails.eval a c220 := h 219 (by decide)
  have h14 : Entails.eval a c500 := derived500 a h
  have h15 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c737 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f737 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c733, some c203, some c158, some c107, some c736, some c734, some c726, some c197, some c219, some c303, some c175, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p737 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked737 : lratChecker f737 p737 = .success := by decide +kernel
theorem unsat737 : Unsatisfiable (PosFin 57) f737 := by
  apply lratCheckerSound f737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p737
  · intro a ha; simp [p737] at ha; subst a; trivial
  · exact checked737
theorem derived737 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c737 := by
  apply localUnsat_implies_entails f737 [c701, c733, c203, c158, c107, c736, c734, c726, c197, c219, c303, c175] c737 unsat737 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c733 := derived733 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c736 := derived736 a h
  have h6 : Entails.eval a c734 := derived734 a h
  have h7 : Entails.eval a c726 := derived726 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c303 := h 302 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c738 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f738 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c737, some c733, some c203, some c138, some c175, some c163, some c261, some c325, some c133, some c197, some c303, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p738 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked738 : lratChecker f738 p738 = .success := by decide +kernel
theorem unsat738 : Unsatisfiable (PosFin 57) f738 := by
  apply lratCheckerSound f738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p738
  · intro a ha; simp [p738] at ha; subst a; trivial
  · exact checked738
theorem derived738 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c738 := by
  apply localUnsat_implies_entails f738 [c701, c737, c733, c203, c138, c175, c163, c261, c325, c133, c197, c303] c738 unsat738 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c175 := h 174 (by decide)
  have h6 : Entails.eval a c163 := h 162 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c303 := h 302 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c739 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f739 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c733, some c203, some c302, some c197, some c303, some c326, some c164, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p739 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked739 : lratChecker f739 p739 = .success := by decide +kernel
theorem unsat739 : Unsatisfiable (PosFin 57) f739 := by
  apply lratCheckerSound f739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p739
  · intro a ha; simp [p739] at ha; subst a; trivial
  · exact checked739
theorem derived739 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c739 := by
  apply localUnsat_implies_entails f739 [c701, c733, c203, c302, c197, c303, c326, c164] c739 unsat739 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c733 := derived733 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c303 := h 302 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c740 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨25, by decide⟩, false), (⟨49, by decide⟩, false), (⟨41, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f740 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c326, some c147, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p740 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked740 : lratChecker f740 p740 = .success := by decide +kernel
theorem unsat740 : Unsatisfiable (PosFin 57) f740 := by
  apply lratCheckerSound f740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p740
  · intro a ha; simp [p740] at ha; subst a; trivial
  · exact checked740
theorem derived740 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c740 := by
  apply localUnsat_implies_entails f740 [c262, c326, c147] c740 unsat740 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c326 := h 325 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c741 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f741 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c737, some c733, some c203, some c738, some c739, some c133, some c740, some c186, some c325, some c261, some c146, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p741 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked741 : lratChecker f741 p741 = .success := by decide +kernel
theorem unsat741 : Unsatisfiable (PosFin 57) f741 := by
  apply lratCheckerSound f741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p741
  · intro a ha; simp [p741] at ha; subst a; trivial
  · exact checked741
theorem derived741 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c741 := by
  apply localUnsat_implies_entails f741 [c701, c737, c733, c203, c738, c739, c133, c740, c186, c325, c261, c146] c741 unsat741 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c737 := derived737 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c738 := derived738 a h
  have h5 : Entails.eval a c739 := derived739 a h
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c740 := derived740 a h
  have h8 : Entails.eval a c186 := h 185 (by decide)
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c742 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨9, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f742 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c741, some c141, some c737, some c733, some c203, some c113, some c186, some c500, some c261, some c157, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p742 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked742 : lratChecker f742 p742 = .success := by decide +kernel
theorem unsat742 : Unsatisfiable (PosFin 57) f742 := by
  apply lratCheckerSound f742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p742
  · intro a ha; simp [p742] at ha; subst a; trivial
  · exact checked742
theorem derived742 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c742 := by
  apply localUnsat_implies_entails f742 [c701, c741, c141, c737, c733, c203, c113, c186, c500, c261, c157] c742 unsat742 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c741 := derived741 a h
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c733 := derived733 a h
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  have h8 : Entails.eval a c500 := derived500 a h
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c743 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f743 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c733, some c203, some c737, some c741, some c141, some c115, some c742, some c262, some c157, some c207, some c261, some c112, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p743 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked743 : lratChecker f743 p743 = .success := by decide +kernel
theorem unsat743 : Unsatisfiable (PosFin 57) f743 := by
  apply lratCheckerSound f743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p743
  · intro a ha; simp [p743] at ha; subst a; trivial
  · exact checked743
theorem derived743 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c743 := by
  apply localUnsat_implies_entails f743 [c701, c733, c203, c737, c741, c141, c115, c742, c262, c157, c207, c261, c112] c743 unsat743 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c733 := derived733 a h
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c737 := derived737 a h
  have h4 : Entails.eval a c741 := derived741 a h
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c115 := h 114 (by decide)
  have h7 : Entails.eval a c742 := derived742 a h
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c157 := h 156 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c744 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f744 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c743, some c4, some c733, some c203, some c46, some c22, some c399, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p744 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked744 : lratChecker f744 p744 = .success := by decide +kernel
theorem unsat744 : Unsatisfiable (PosFin 57) f744 := by
  apply lratCheckerSound f744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p744
  · intro a ha; simp [p744] at ha; subst a; trivial
  · exact checked744
theorem derived744 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c744 := by
  apply localUnsat_implies_entails f744 [c700, c701, c743, c4, c733, c203, c46, c22, c399] c744 unsat744 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c743 := derived743 a h
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c733 := derived733 a h
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c399 := derived399 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c745 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨41, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f745 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c744, some c733, some c7, some c203, some c743, some c4, some c652, some c740, some c261, some c186, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p745 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked745 : lratChecker f745 p745 = .success := by decide +kernel
theorem unsat745 : Unsatisfiable (PosFin 57) f745 := by
  apply lratCheckerSound f745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p745
  · intro a ha; simp [p745] at ha; subst a; trivial
  · exact checked745
theorem derived745 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c745 := by
  apply localUnsat_implies_entails f745 [c700, c701, c744, c733, c7, c203, c743, c4, c652, c740, c261, c186] c745 unsat745 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c744 := derived744 a h
  have h3 : Entails.eval a c733 := derived733 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c743 := derived743 a h
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c652 := derived652 a h
  have h9 : Entails.eval a c740 := derived740 a h
  have h10 : Entails.eval a c261 := h 260 (by decide)
  have h11 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c746 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f746 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c700, some c701, some c744, some c743, some c4, some c733, some c203, some c745, some c38, some c739, some c175, some c163, some c303, some c325, some c197, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p746 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked746 : lratChecker f746 p746 = .success := by decide +kernel
theorem unsat746 : Unsatisfiable (PosFin 57) f746 := by
  apply lratCheckerSound f746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p746
  · intro a ha; simp [p746] at ha; subst a; trivial
  · exact checked746
theorem derived746 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c746 := by
  apply localUnsat_implies_entails f746 [c700, c701, c744, c743, c4, c733, c203, c745, c38, c739, c175, c163, c303, c325, c197] c746 unsat746 (by rfl) a
  have h0 : Entails.eval a c700 := derived700 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c744 := derived744 a h
  have h3 : Entails.eval a c743 := derived743 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c733 := derived733 a h
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c745 := derived745 a h
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c739 := derived739 a h
  have h10 : Entails.eval a c175 := h 174 (by decide)
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c303 := h 302 (by decide)
  have h13 : Entails.eval a c325 := h 324 (by decide)
  have h14 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c747 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f747 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c701, some c700, some c733, some c203, some c743, some c4, some c744, some c746, some c63, some c15, some c734, some c726, some c197, some c219, some c303, some c175, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p747 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked747 : lratChecker f747 p747 = .success := by decide +kernel
theorem unsat747 : Unsatisfiable (PosFin 57) f747 := by
  apply lratCheckerSound f747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p747
  · intro a ha; simp [p747] at ha; subst a; trivial
  · exact checked747
theorem derived747 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c747 := by
  apply localUnsat_implies_entails f747 [c701, c700, c733, c203, c743, c4, c744, c746, c63, c15, c734, c726, c197, c219, c303, c175] c747 unsat747 (by rfl) a
  have h0 : Entails.eval a c701 := derived701 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c733 := derived733 a h
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c743 := derived743 a h
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c744 := derived744 a h
  have h7 : Entails.eval a c746 := derived746 a h
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c734 := derived734 a h
  have h11 : Entails.eval a c726 := derived726 a h
  have h12 : Entails.eval a c197 := h 196 (by decide)
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c303 := h 302 (by decide)
  have h15 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c748 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f748 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c701, some c200, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p748 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked748 : lratChecker f748 p748 = .success := by decide +kernel
theorem unsat748 : Unsatisfiable (PosFin 57) f748 := by
  apply lratCheckerSound f748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p748
  · intro a ha; simp [p748] at ha; subst a; trivial
  · exact checked748
theorem derived748 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c748 := by
  apply localUnsat_implies_entails f748 [c747, c701, c200] c748 unsat748 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c701 := derived701 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c749 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f749 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c747, some c700, some c701, some c14, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p749 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked749 : lratChecker f749 p749 = .success := by decide +kernel
theorem unsat749 : Unsatisfiable (PosFin 57) f749 := by
  apply lratCheckerSound f749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p749
  · intro a ha; simp [p749] at ha; subst a; trivial
  · exact checked749
theorem derived749 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c749 := by
  apply localUnsat_implies_entails f749 [c747, c700, c701, c14] c749 unsat749 (by rfl) a
  have h0 : Entails.eval a c747 := derived747 a h
  have h1 : Entails.eval a c700 := derived700 a h
  have h2 : Entails.eval a c701 := derived701 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c750 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨17, by decide⟩, false), (⟨14, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f750 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c163, some c219, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p750 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked750 : lratChecker f750 p750 = .success := by decide +kernel
theorem unsat750 : Unsatisfiable (PosFin 57) f750 := by
  apply lratCheckerSound f750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p750
  · intro a ha; simp [p750] at ha; subst a; trivial
  · exact checked750
theorem derived750 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c750 := by
  apply localUnsat_implies_entails f750 [c112, c163, c219] c750 unsat750 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c751 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨17, by decide⟩, false), (⟨33, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f751 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c302, some c219, some c726, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p751 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked751 : lratChecker f751 p751 = .success := by decide +kernel
theorem unsat751 : Unsatisfiable (PosFin 57) f751 := by
  apply lratCheckerSound f751 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p751
  · intro a ha; simp [p751] at ha; subst a; trivial
  · exact checked751
theorem derived751 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c751 := by
  apply localUnsat_implies_entails f751 [c302, c219, c726] c751 unsat751 (by rfl) a
  have h0 : Entails.eval a c302 := h 301 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c726 := derived726 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c752 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨14, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f752 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c748, some c749, some c700, some c133, some c107, some c750, some c751, some c138, some c668, some c100, some c104, some c54, some c81, some c266, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p752 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked752 : lratChecker f752 p752 = .success := by decide +kernel
theorem unsat752 : Unsatisfiable (PosFin 57) f752 := by
  apply lratCheckerSound f752 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p752
  · intro a ha; simp [p752] at ha; subst a; trivial
  · exact checked752
theorem derived752 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c752 := by
  apply localUnsat_implies_entails f752 [c748, c749, c700, c133, c107, c750, c751, c138, c668, c100, c104, c54, c81, c266] c752 unsat752 (by rfl) a
  have h0 : Entails.eval a c748 := derived748 a h
  have h1 : Entails.eval a c749 := derived749 a h
  have h2 : Entails.eval a c700 := derived700 a h
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c750 := derived750 a h
  have h6 : Entails.eval a c751 := derived751 a h
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c668 := derived668 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived752

end CochromaticTwenty.Certificates.B16_5_2
