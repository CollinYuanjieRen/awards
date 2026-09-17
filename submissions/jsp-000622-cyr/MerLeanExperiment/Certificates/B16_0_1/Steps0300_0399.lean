import MerLeanExperiment.Certificates.B16_0_1.Steps0200_0299

/-! Generated from the actual pinned b16_0_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c627 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c626, some c26, some c8, some c35, some c291, some c293, some c580, some c138, some c21, some c1, some c239, some c241, some c204, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c626, c26, c8, c35, c291, c293, c580, c138, c21, c1, c239, c241, c204] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c626 := derived626 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c580 := derived580 a h
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c241 := h 240 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨37, by decide⟩, false), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c98, some c26, some c8, some c35, some c300, some c603, some c223, some c21, some c56, some c499, some c231, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c97, c98, c26, c8, c35, c300, c603, c223, c21, c56, c499, c231] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c300 := h 299 (by decide)
  have h6 : Entails.eval a c603 := derived603 a h
  have h7 : Entails.eval a c223 := h 222 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c499 := derived499 a h
  have h11 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c615, some c619, some c98, some c97, some c624, some c96, some c627, some c54, some c19, some c63, some c628, some c623, some c240, some c223, some c31, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c547, c615, c619, c98, c97, c624, c96, c627, c54, c19, c63, c628, c623, c240, c223, c31] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c615 := derived615 a h
  have h2 : Entails.eval a c619 := derived619 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c624 := derived624 a h
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c627 := derived627 a h
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c628 := derived628 a h
  have h12 : Entails.eval a c623 := derived623 a h
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c99, some c96, some c97, some c625, some c249, some c31, some c21, some c54, some c63, some c437, some c223, some c300, some c282, some c499, some c84, some c320, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c547, c99, c96, c97, c625, c249, c31, c21, c54, c63, c437, c223, c300, c282, c499, c84, c320] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c625 := derived625 a h
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c437 := derived437 a h
  have h11 : Entails.eval a c223 := h 222 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c499 := derived499 a h
  have h15 : Entails.eval a c84 := h 83 (by decide)
  have h16 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c99, some c96, some c97, some c625, some c249, some c31, some c3, some c21, some c250, some c243, some c630, some c290, some c134, some c204, some c10, some c292, some c144, some c68, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c547, c99, c96, c97, c625, c249, c31, c3, c21, c250, c243, c630, c290, c134, c204, c10, c292, c144, c68] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c625 := derived625 a h
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c243 := h 242 (by decide)
  have h11 : Entails.eval a c630 := derived630 a h
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c134 := h 133 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨24, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c96, some c97, some c625, some c249, some c21, some c3, some c631, some c1, some c19, some c134, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c547, c96, c97, c625, c249, c21, c3, c631, c1, c19, c134] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c625 := derived625 a h
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c19 := h 18 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c1, some c443, some c134, some c180, some c13, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c19, c1, c443, c134, c180, c13] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c443 := derived443 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c19, some c633, some c66, some c65, some c292, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c19, c633, c66, c65, c292] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c633 := derived633 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c634, some c240, some c242, some c30, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c634, c240, c242, c30] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c634 := derived634 a h
  have h1 : Entails.eval a c240 := h 239 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c96, some c99, some c632, some c635, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c547, c96, c99, c632, c635] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c632 := derived632 a h
  have h4 : Entails.eval a c635 := derived635 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c31, some c30, some c241, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c31, c30, c241] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨23, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c294, some c208, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c591, c294, c208] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c99, some c96, some c637, some c54, some c594, some c221, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c547, c99, c96, c637, c54, c594, c221] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c637 := derived637 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c594 := derived594 a h
  have h6 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c547, some c96, some c99, some c637, some c239, some c639, some c591, some c638, some c208, some c66, some c290, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c636, c547, c96, c99, c637, c239, c639, c591, c638, c208, c66, c290] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c637 := derived637 a h
  have h5 : Entails.eval a c239 := h 238 (by decide)
  have h6 : Entails.eval a c639 := derived639 a h
  have h7 : Entails.eval a c591 := derived591 a h
  have h8 : Entails.eval a c638 := derived638 a h
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c638, some c208, some c66, some c290, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c591, c638, c208, c66, c290] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c636, some c547, some c96, some c99, some c640, some c19, some c591, some c201, some c641, some c248, some c245, some c31, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c636, c547, c96, c99, c640, c19, c591, c201, c641, c248, c245, c31] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c636 := derived636 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c99 := h 98 (by decide)
  have h4 : Entails.eval a c640 := derived640 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c591 := derived591 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c641 := derived641 a h
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨33, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c21, some c3, some c134, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c21, c3, c134] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c642, some c97, some c636, some c96, some c99, some c1, some c19, some c28, some c643, some c244, some c201, some c291, some c56, some c66, some c231, some c136, some c81, some c13, some c160, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c547, c642, c97, c636, c96, c99, c1, c19, c28, c643, c244, c201, c291, c56, c66, c231, c136, c81, c13, c160] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c642 := derived642 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c636 := derived636 a h
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c643 := derived643 a h
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c291 := h 290 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c231 := h 230 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c56, some c66, some c221, some c294, some c292, some c81, some c204, some c231, some c241, some c33, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c239, c56, c66, c221, c294, c292, c81, c204, c231, c241, c33] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c294 := h 293 (by decide)
  have h5 : Entails.eval a c292 := h 291 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c241 := h 240 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c645, some c290, some c291, some c208, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c239, c645, c290, c291, c208] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c645 := derived645 a h
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c291 := h 290 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c644, some c547, some c642, some c97, some c636, some c96, some c99, some c646, some c54, some c63, some c221, some c56, some c84, some c300, some c223, some c201, some c33, some c244, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c644, c547, c642, c97, c636, c96, c99, c646, c54, c63, c221, c56, c84, c300, c223, c201, c33, c244] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c644 := derived644 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c642 := derived642 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c636 := derived636 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c646 := derived646 a h
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c300 := h 299 (by decide)
  have h14 : Entails.eval a c223 := h 222 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c33 := h 32 (by decide)
  have h17 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨22, by decide⟩, false), (⟨11, by decide⟩, false), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c54, some c63, some c223, some c144, some c84, some c10, some c160, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c54, c63, c223, c144, c84, c10, c160] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c54 := h 53 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c223 := h 222 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c99, some c96, some c636, some c642, some c97, some c644, some c647, some c21, some c3, some c31, some c243, some c648, some c290, some c291, some c208, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c547, c99, c96, c636, c642, c97, c644, c647, c21, c3, c31, c243, c648, c290, c291, c208] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c636 := derived636 a h
  have h4 : Entails.eval a c642 := derived642 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c644 := derived644 a h
  have h7 : Entails.eval a c647 := derived647 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c648 := derived648 a h
  have h13 : Entails.eval a c290 := h 289 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c21, some c290, some c291, some c25, some c243, some c31, some c98, some c67, some c436, some c292, some c207, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c21, c290, c291, c25, c243, c31, c98, c67, c436, c292, c207] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c21 := h 20 (by decide)
  have h1 : Entails.eval a c290 := h 289 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c436 := derived436 a h
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c650, some c30, some c222, some c83, some c85, some c480, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c547, c650, c30, c222, c83, c85, c480] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c650 := derived650 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c480 := derived480 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c547, some c21, some c3, some c650, some c54, some c651, some c98, some c97, some c31, some c648, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c649, c547, c21, c3, c650, c54, c651, c98, c97, c31, c648] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c651 := derived651 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c648 := derived648 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨49, by decide⟩, false), (⟨15, by decide⟩, false), (⟨39, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c145, some c84, some c13, some c223, some c151, some c24, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c56, c145, c84, c13, c223, c151, c24] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c223 := h 222 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c7, some c25, some c221, some c653, some c98, some c32, some c83, some c222, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c239, c7, c25, c221, c653, c98, c32, c83, c222] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c653 := derived653 a h
  have h5 : Entails.eval a c98 := h 97 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c222 := h 221 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c547, some c652, some c239, some c240, some c25, some c654, some c54, some c290, some c294, some c66, some c98, some c591, some c32, some c207, some c241, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c649, c547, c652, c239, c240, c25, c654, c54, c290, c294, c66, c98, c591, c32, c207, c241] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c240 := h 239 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c654 := derived654 a h
  have h7 : Entails.eval a c54 := h 53 (by decide)
  have h8 : Entails.eval a c290 := h 289 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c591 := derived591 a h
  have h13 : Entails.eval a c32 := h 31 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c7, some c137, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c25, c7, c137] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨33, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c290, some c137, some c65, some c14, some c135, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c290, c137, c65, c14, c135] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c290 := h 289 (by decide)
  have h1 : Entails.eval a c137 := h 136 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c1, some c19, some c643, some c649, some c656, some c245, some c591, some c201, some c440, some c282, some c657, some c60, some c67, some c324, some c292, some c288, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c655, c1, c19, c643, c649, c656, c245, c591, c201, c440, c282, c657, c60, c67, c324, c292, c288] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c643 := derived643 a h
  have h4 : Entails.eval a c649 := derived649 a h
  have h5 : Entails.eval a c656 := derived656 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c591 := derived591 a h
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c440 := derived440 a h
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c657 := derived657 a h
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c67 := h 66 (by decide)
  have h14 : Entails.eval a c324 := h 323 (by decide)
  have h15 : Entails.eval a c292 := h 291 (by decide)
  have h16 : Entails.eval a c288 := h 287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c547, some c655, some c1, some c19, some c643, some c656, some c245, some c658, some c98, some c97, some c28, some c249, some c201, some c291, some c580, some c56, some c60, some c232, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c649, c547, c655, c1, c19, c643, c656, c245, c658, c98, c97, c28, c249, c201, c291, c580, c56, c60, c232] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c643 := derived643 a h
  have h6 : Entails.eval a c656 := derived656 a h
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c658 := derived658 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c28 := h 27 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c580 := derived580 a h
  have h16 : Entails.eval a c56 := h 55 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨10, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c185, some c129, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c183, c185, c129] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c15, some c182, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c16, c15, c182] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c291, some c293, some c138, some c109, some c48, some c51, some c660, some c112, some c245, some c248, some c202, some c33, some c246, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c100, c291, c293, c138, c109, c48, c51, c660, c112, c245, c248, c202, c33, c246] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c293 := h 292 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c660 := derived660 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c6, some c136, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c24, c6, c136] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨23, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c663, some c248, some c629, some c662, some c201, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c663, c248, c629, c662, c201] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c663 := derived663 a h
  have h1 : Entails.eval a c248 := h 247 (by decide)
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c662 := derived662 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨36, by decide⟩, true), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c249, some c250, some c202, some c134, some c113, some c104, some c185, some c42, some c103, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c249, c250, c202, c134, c113, c104, c185, c42, c103] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c249 := h 248 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c185 := h 184 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c25, some c60, some c629, some c659, some c100, some c547, some c661, some c663, some c243, some c248, some c238, some c28, some c59, some c292, some c665, some c67, some c662, some c201, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c649, c25, c60, c629, c659, c100, c547, c661, c663, c243, c248, c238, c28, c59, c292, c665, c67, c662, c201] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c60 := h 59 (by decide)
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c661 := derived661 a h
  have h8 : Entails.eval a c663 := derived663 a h
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c238 := h 237 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c665 := derived665 a h
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c662 := derived662 a h
  have h18 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c649, some c547, some c666, some c98, some c67, some c293, some c292, some c135, some c4, some c512, some c201, some c242, some c439, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c629, c659, c100, c649, c547, c666, c98, c67, c293, c292, c135, c4, c512, c201, c242, c439] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c649 := derived649 a h
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c666 := derived666 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c292 := h 291 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c512 := derived512 a h
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c439 := derived439 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨13, by decide⟩, false), (⟨17, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c25, some c243, some c67, some c293, some c292, some c147, some c207, some c4, some c242, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c25, c243, c67, c293, c292, c147, c207, c4, c242] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c25 := h 24 (by decide)
  have h1 : Entails.eval a c243 := h 242 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c292 := h 291 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c25, some c667, some c1, some c243, some c547, some c629, some c659, some c100, some c69, some c10, some c668, some c98, some c24, some c292, some c60, some c224, some c81, some c239, some c242, some c469, some c202, some c291, some c144, some c282, some c104, some c167, some c42, some c251, some c127, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c649, c25, c667, c1, c243, c547, c629, c659, c100, c69, c10, c668, c98, c24, c292, c60, c224, c81, c239, c242, c469, c202, c291, c144, c282, c104, c167, c42, c251, c127] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c667 := derived667 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c547 := derived547 a h
  have h6 : Entails.eval a c629 := derived629 a h
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c668 := derived668 a h
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c224 := h 223 (by decide)
  have h17 : Entails.eval a c81 := h 80 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c242 := h 241 (by decide)
  have h20 : Entails.eval a c469 := derived469 a h
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c291 := h 290 (by decide)
  have h23 : Entails.eval a c144 := h 143 (by decide)
  have h24 : Entails.eval a c282 := h 281 (by decide)
  have h25 : Entails.eval a c104 := h 103 (by decide)
  have h26 : Entails.eval a c167 := h 166 (by decide)
  have h27 : Entails.eval a c42 := h 41 (by decide)
  have h28 : Entails.eval a c251 := h 250 (by decide)
  have h29 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨36, by decide⟩, true), (⟨21, by decide⟩, false), (⟨53, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, false), (⟨37, by decide⟩, false), (⟨23, by decide⟩, false), (⟨55, by decide⟩, false), (⟨3, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c201, some c230, some c246, some c282, some c202, some c176, some c144, some c109, some c104, some c48, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c629, c201, c230, c246, c282, c202, c176, c144, c109, c104, c48] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c246 := h 245 (by decide)
  have h4 : Entails.eval a c282 := h 281 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c48 := h 47 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c649, some c547, some c60, some c25, some c69, some c667, some c1, some c10, some c239, some c243, some c224, some c81, some c668, some c98, some c24, some c33, some c292, some c669, some c670, some c291, some c150, some c202, some c109, some c246, some c48, some c51, some c112, some c660, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c629, c659, c100, c649, c547, c60, c25, c69, c667, c1, c10, c239, c243, c224, c81, c668, c98, c24, c33, c292, c669, c670, c291, c150, c202, c109, c246, c48, c51, c112, c660] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c649 := derived649 a h
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c667 := derived667 a h
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c239 := h 238 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c81 := h 80 (by decide)
  have h15 : Entails.eval a c668 := derived668 a h
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c24 := h 23 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  have h19 : Entails.eval a c292 := h 291 (by decide)
  have h20 : Entails.eval a c669 := derived669 a h
  have h21 : Entails.eval a c670 := derived670 a h
  have h22 : Entails.eval a c291 := h 290 (by decide)
  have h23 : Entails.eval a c150 := h 149 (by decide)
  have h24 : Entails.eval a c202 := h 201 (by decide)
  have h25 : Entails.eval a c109 := h 108 (by decide)
  have h26 : Entails.eval a c246 := h 245 (by decide)
  have h27 : Entails.eval a c48 := h 47 (by decide)
  have h28 : Entails.eval a c51 := h 50 (by decide)
  have h29 : Entails.eval a c112 := h 111 (by decide)
  have h30 : Entails.eval a c660 := derived660 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨36, by decide⟩, true), (⟨17, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c241, some c203, some c24, some c239, some c98, some c34, some c57, some c222, some c234, some c81, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c241, c203, c24, c239, c98, c34, c57, c222, c234, c81] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c241 := h 240 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c222 := h 221 (by decide)
  have h8 : Entails.eval a c234 := h 233 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨18, by decide⟩, true), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c112, some c48, some c51, some c660, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c109, c112, c48, c51, c660] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c660 := derived660 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c10, some c1, some c671, some c294, some c290, some c649, some c547, some c672, some c22, some c202, some c98, some c239, some c68, some c34, some c244, some c673, some c201, some c150, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c629, c659, c100, c10, c1, c671, c294, c290, c649, c547, c672, c22, c202, c98, c239, c68, c34, c244, c673, c201, c150] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c649 := derived649 a h
  have h9 : Entails.eval a c547 := derived547 a h
  have h10 : Entails.eval a c672 := derived672 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c239 := h 238 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c34 := h 33 (by decide)
  have h17 : Entails.eval a c244 := h 243 (by decide)
  have h18 : Entails.eval a c673 := derived673 a h
  have h19 : Entails.eval a c201 := h 200 (by decide)
  have h20 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c10, some c1, some c671, some c294, some c649, some c547, some c674, some c293, some c201, some c207, some c512, some c243, some c32, some c98, some c59, some c68, some c223, some c229, some c147, some c81, some c282, some c105, some c176, some c51, some c109, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c629, c659, c100, c10, c1, c671, c294, c649, c547, c674, c293, c201, c207, c512, c243, c32, c98, c59, c68, c223, c229, c147, c81, c282, c105, c176, c51, c109] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c294 := h 293 (by decide)
  have h7 : Entails.eval a c649 := derived649 a h
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c674 := derived674 a h
  have h10 : Entails.eval a c293 := h 292 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c207 := h 206 (by decide)
  have h13 : Entails.eval a c512 := derived512 a h
  have h14 : Entails.eval a c243 := h 242 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c59 := h 58 (by decide)
  have h18 : Entails.eval a c68 := h 67 (by decide)
  have h19 : Entails.eval a c223 := h 222 (by decide)
  have h20 : Entails.eval a c229 := h 228 (by decide)
  have h21 : Entails.eval a c147 := h 146 (by decide)
  have h22 : Entails.eval a c81 := h 80 (by decide)
  have h23 : Entails.eval a c282 := h 281 (by decide)
  have h24 : Entails.eval a c105 := h 104 (by decide)
  have h25 : Entails.eval a c176 := h 175 (by decide)
  have h26 : Entails.eval a c51 := h 50 (by decide)
  have h27 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c671, some c294, some c290, some c629, some c659, some c100, some c649, some c547, some c1, some c10, some c675, some c242, some c240, some c202, some c203, some c243, some c7, some c32, some c98, some c68, some c147, some c105, some c113, some c43, some c51, some c184, some c188, some c128, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c671, c294, c290, c629, c659, c100, c649, c547, c1, c10, c675, c242, c240, c202, c203, c243, c7, c32, c98, c68, c147, c105, c113, c43, c51, c184, c188, c128] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c671 := derived671 a h
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c649 := derived649 a h
  have h7 : Entails.eval a c547 := derived547 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  have h10 : Entails.eval a c675 := derived675 a h
  have h11 : Entails.eval a c242 := h 241 (by decide)
  have h12 : Entails.eval a c240 := h 239 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c243 := h 242 (by decide)
  have h16 : Entails.eval a c7 := h 6 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c98 := h 97 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c147 := h 146 (by decide)
  have h21 : Entails.eval a c105 := h 104 (by decide)
  have h22 : Entails.eval a c113 := h 112 (by decide)
  have h23 : Entails.eval a c43 := h 42 (by decide)
  have h24 : Entails.eval a c51 := h 50 (by decide)
  have h25 : Entails.eval a c184 := h 183 (by decide)
  have h26 : Entails.eval a c188 := h 187 (by decide)
  have h27 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c629, some c659, some c100, some c671, some c676, some c137, some c16, some c656, some c547, some c135, some c14, some c98, some c664, some c663, some c243, some c248, some c28, some c250, some c105, some c252, some c43, some c190, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c649, c629, c659, c100, c671, c676, c137, c16, c656, c547, c135, c14, c98, c664, c663, c243, c248, c28, c250, c105, c252, c43, c190] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c676 := derived676 a h
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c656 := derived656 a h
  have h9 : Entails.eval a c547 := derived547 a h
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c664 := derived664 a h
  have h14 : Entails.eval a c663 := derived663 a h
  have h15 : Entails.eval a c243 := h 242 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c28 := h 27 (by decide)
  have h18 : Entails.eval a c250 := h 249 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c252 := h 251 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c677, some c649, some c629, some c659, some c100, some c671, some c676, some c137, some c16, some c656, some c290, some c547, some c22, some c202, some c98, some c664, some c239, some c249, some c28, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c677, c649, c629, c659, c100, c671, c676, c137, c16, c656, c290, c547, c22, c202, c98, c664, c239, c249, c28] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c677 := derived677 a h
  have h1 : Entails.eval a c649 := derived649 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c676 := derived676 a h
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c290 := h 289 (by decide)
  have h11 : Entails.eval a c547 := derived547 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c664 := derived664 a h
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c249 := h 248 (by decide)
  have h18 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c649, some c547, some c671, some c290, some c294, some c676, some c137, some c16, some c677, some c678, some c672, some c28, some c246, some c250, some c201, some c138, some c112, some c673, some c185, some c14, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c629, c659, c100, c649, c547, c671, c290, c294, c676, c137, c16, c677, c678, c672, c28, c246, c250, c201, c138, c112, c673, c185, c14] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c649 := derived649 a h
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c671 := derived671 a h
  have h6 : Entails.eval a c290 := h 289 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  have h8 : Entails.eval a c676 := derived676 a h
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c677 := derived677 a h
  have h12 : Entails.eval a c678 := derived678 a h
  have h13 : Entails.eval a c672 := derived672 a h
  have h14 : Entails.eval a c28 := h 27 (by decide)
  have h15 : Entails.eval a c246 := h 245 (by decide)
  have h16 : Entails.eval a c250 := h 249 (by decide)
  have h17 : Entails.eval a c201 := h 200 (by decide)
  have h18 : Entails.eval a c138 := h 137 (by decide)
  have h19 : Entails.eval a c112 := h 111 (by decide)
  have h20 : Entails.eval a c673 := derived673 a h
  have h21 : Entails.eval a c185 := h 184 (by decide)
  have h22 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨36, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c679, some c63, some c19, some c54, some c649, some c547, some c584, some c222, some c242, some c57, some c98, some c661, some c33, some c246, some c201, some c673, some c150, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c629, c659, c100, c679, c63, c19, c54, c649, c547, c584, c222, c242, c57, c98, c661, c33, c246, c201, c673, c150] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c679 := derived679 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c649 := derived649 a h
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c584 := derived584 a h
  have h10 : Entails.eval a c222 := h 221 (by decide)
  have h11 : Entails.eval a c242 := h 241 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c98 := h 97 (by decide)
  have h14 : Entails.eval a c661 := derived661 a h
  have h15 : Entails.eval a c33 := h 32 (by decide)
  have h16 : Entails.eval a c246 := h 245 (by decide)
  have h17 : Entails.eval a c201 := h 200 (by decide)
  have h18 : Entails.eval a c673 := derived673 a h
  have h19 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c679, some c63, some c201, some c673, some c150, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c629, c659, c100, c679, c63, c201, c673, c150] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c679 := derived679 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c673 := derived673 a h
  have h7 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨36, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c649, some c629, some c659, some c100, some c547, some c680, some c22, some c98, some c661, some c679, some c63, some c202, some c144, some c104, some c113, some c42, some c48, some c181, some c185, some c128, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c649, c629, c659, c100, c547, c680, c22, c98, c661, c679, c63, c202, c144, c104, c113, c42, c48, c181, c185, c128] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c649 := derived649 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c680 := derived680 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c661 := derived661 a h
  have h9 : Entails.eval a c679 := derived679 a h
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c48 := h 47 (by decide)
  have h17 : Entails.eval a c181 := h 180 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c679, some c19, some c629, some c659, some c100, some c649, some c547, some c680, some c22, some c98, some c661, some c682, some c239, some c34, some c240, some c244, some c681, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c679, c19, c629, c659, c100, c649, c547, c680, c22, c98, c661, c682, c239, c34, c240, c244, c681] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c679 := derived679 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c649 := derived649 a h
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c680 := derived680 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c661 := derived661 a h
  have h11 : Entails.eval a c682 := derived682 a h
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c240 := h 239 (by decide)
  have h15 : Entails.eval a c244 := h 243 (by decide)
  have h16 : Entails.eval a c681 := derived681 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c547, some c105, some c43, some c201, some c103, some c240, some c183, some c113, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c4, c547, c105, c43, c201, c103, c240, c183, c113] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c240 := h 239 (by decide)
  have h7 : Entails.eval a c183 := h 182 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨32, by decide⟩, true), (⟨26, by decide⟩, true), (⟨13, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c179, some c183, some c128, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c179, c183, c128] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c179 := h 178 (by decide)
  have h1 : Entails.eval a c183 := h 182 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c679, some c63, some c683, some c301, some c19, some c649, some c547, some c147, some c4, some c105, some c43, some c51, some c684, some c685, some c113, some c239, some c244, some c34, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c629, c659, c100, c679, c63, c683, c301, c19, c649, c547, c147, c4, c105, c43, c51, c684, c685, c113, c239, c244, c34] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c679 := derived679 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c301 := h 300 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c649 := derived649 a h
  have h9 : Entails.eval a c547 := derived547 a h
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c684 := derived684 a h
  have h16 : Entails.eval a c685 := derived685 a h
  have h17 : Entails.eval a c113 := h 112 (by decide)
  have h18 : Entails.eval a c239 := h 238 (by decide)
  have h19 : Entails.eval a c244 := h 243 (by decide)
  have h20 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c679, some c54, some c629, some c659, some c100, some c649, some c547, some c686, some c16, some c661, some c163, some c98, some c85, some c4, some c161, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c679, c54, c629, c659, c100, c649, c547, c686, c16, c661, c163, c98, c85, c4, c161] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c679 := derived679 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c649 := derived649 a h
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c686 := derived686 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c661 := derived661 a h
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c85 := h 84 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c679, some c63, some c19, some c54, some c649, some c547, some c683, some c301, some c687, some c584, some c222, some c242, some c201, some c246, some c34, some c33, some c224, some c98, some c85, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c629, c659, c100, c679, c63, c19, c54, c649, c547, c683, c301, c687, c584, c222, c242, c201, c246, c34, c33, c224, c98, c85] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c679 := derived679 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c649 := derived649 a h
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c683 := derived683 a h
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c687 := derived687 a h
  have h12 : Entails.eval a c584 := derived584 a h
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c246 := h 245 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  have h19 : Entails.eval a c224 := h 223 (by decide)
  have h20 : Entails.eval a c98 := h 97 (by decide)
  have h21 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c679, some c19, some c242, some c54, some c222, some c629, some c659, some c100, some c63, some c649, some c57, some c85, some c301, some c224, some c201, some c34, some c246, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c679, c19, c242, c54, c222, c629, c659, c100, c63, c649, c57, c85, c301, c224, c201, c34, c246] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c679 := derived679 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c222 := h 221 (by decide)
  have h5 : Entails.eval a c629 := derived629 a h
  have h6 : Entails.eval a c659 := derived659 a h
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c649 := derived649 a h
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c301 := h 300 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c201 := h 200 (by decide)
  have h15 : Entails.eval a c34 := h 33 (by decide)
  have h16 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c688, some c10, some c679, some c19, some c547, some c584, some c242, some c689, some c98, some c681, some c33, some c246, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c629, c659, c100, c688, c10, c679, c19, c547, c584, c242, c689, c98, c681, c33, c246] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c688 := derived688 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c679 := derived679 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c547 := derived547 a h
  have h8 : Entails.eval a c584 := derived584 a h
  have h9 : Entails.eval a c242 := h 241 (by decide)
  have h10 : Entails.eval a c689 := derived689 a h
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c681 := derived681 a h
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c690, some c629, some c659, some c100, some c688, some c10, some c679, some c63, some c301, some c147, some c282, some c105, some c176, some c51, some c109, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c690, c629, c659, c100, c688, c10, c679, c63, c301, c147, c282, c105, c176, c51, c109] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c688 := derived688 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c679 := derived679 a h
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c301 := h 300 (by decide)
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  have h13 : Entails.eval a c51 := h 50 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨24, by decide⟩, true), (⟨21, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c244, some c690, some c629, some c659, some c100, some c688, some c10, some c679, some c63, some c228, some c691, some c202, some c300, some c144, some c282, some c104, some c176, some c48, some c109, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c244, c690, c629, c659, c100, c688, c10, c679, c63, c228, c691, c202, c300, c144, c282, c104, c176, c48, c109] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c244 := h 243 (by decide)
  have h1 : Entails.eval a c690 := derived690 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c688 := derived688 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c679 := derived679 a h
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  have h10 : Entails.eval a c691 := derived691 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c300 := h 299 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  have h14 : Entails.eval a c282 := h 281 (by decide)
  have h15 : Entails.eval a c104 := h 103 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c499, some c87, some c319, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c499, c87, c319] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c499 := derived499 a h
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c649, some c629, some c659, some c100, some c679, some c54, some c693, some c690, some c63, some c244, some c228, some c692, some c437, some c282, some c300, some c301, some c202, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c547, c649, c629, c659, c100, c679, c54, c693, c690, c63, c244, c228, c692, c437, c282, c300, c301, c202] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c649 := derived649 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c679 := derived679 a h
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c693 := derived693 a h
  have h8 : Entails.eval a c690 := derived690 a h
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c692 := derived692 a h
  have h13 : Entails.eval a c437 := derived437 a h
  have h14 : Entails.eval a c282 := h 281 (by decide)
  have h15 : Entails.eval a c300 := h 299 (by decide)
  have h16 : Entails.eval a c301 := h 300 (by decide)
  have h17 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c33, some c243, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c34, c33, c243] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c679, some c19, some c629, some c659, some c100, some c688, some c10, some c649, some c547, some c98, some c695, some c694, some c681, some c240, some c437, some c54, some c693, some c63, some c300, some c144, some c282, some c104, some c167, some c42, some c103, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c679, c19, c629, c659, c100, c688, c10, c649, c547, c98, c695, c694, c681, c240, c437, c54, c693, c63, c300, c144, c282, c104, c167, c42, c103] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c679 := derived679 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c688 := derived688 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c649 := derived649 a h
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c695 := derived695 a h
  have h11 : Entails.eval a c694 := derived694 a h
  have h12 : Entails.eval a c681 := derived681 a h
  have h13 : Entails.eval a c240 := h 239 (by decide)
  have h14 : Entails.eval a c437 := derived437 a h
  have h15 : Entails.eval a c54 := h 53 (by decide)
  have h16 : Entails.eval a c693 := derived693 a h
  have h17 : Entails.eval a c63 := h 62 (by decide)
  have h18 : Entails.eval a c300 := h 299 (by decide)
  have h19 : Entails.eval a c144 := h 143 (by decide)
  have h20 : Entails.eval a c282 := h 281 (by decide)
  have h21 : Entails.eval a c104 := h 103 (by decide)
  have h22 : Entails.eval a c167 := h 166 (by decide)
  have h23 : Entails.eval a c42 := h 41 (by decide)
  have h24 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c690, some c629, some c659, some c100, some c688, some c10, some c679, some c63, some c19, some c649, some c547, some c98, some c695, some c694, some c681, some c240, some c696, some c202, some c301, some c147, some c684, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c690, c629, c659, c100, c688, c10, c679, c63, c19, c649, c547, c98, c695, c694, c681, c240, c696, c202, c301, c147, c684] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c688 := derived688 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c679 := derived679 a h
  have h7 : Entails.eval a c63 := h 62 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c649 := derived649 a h
  have h10 : Entails.eval a c547 := derived547 a h
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c695 := derived695 a h
  have h13 : Entails.eval a c694 := derived694 a h
  have h14 : Entails.eval a c681 := derived681 a h
  have h15 : Entails.eval a c240 := h 239 (by decide)
  have h16 : Entails.eval a c696 := derived696 a h
  have h17 : Entails.eval a c202 := h 201 (by decide)
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c684 := derived684 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c659, some c100, some c679, some c63, some c688, some c10, some c690, some c697, some c22, some c4, some c147, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c629, c659, c100, c679, c63, c688, c10, c690, c697, c22, c4, c147] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c659 := derived659 a h
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c679 := derived679 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c688 := derived688 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c690 := derived690 a h
  have h8 : Entails.eval a c697 := derived697 a h
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨40, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c426, some c244, some c201, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c629, c698, c91, c93, c426, c244, c201] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c244 := h 243 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c629, some c698, some c93, some c4, some c22, some c147, some c91, some c30, some c585, some c699, some c5, some c106, some c44, some c52, some c192, some c240, some c199, some c111, some c135, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c547, c629, c698, c93, c4, c22, c147, c91, c30, c585, c699, c5, c106, c44, c52, c192, c240, c199, c111, c135] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c147 := h 146 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c585 := derived585 a h
  have h10 : Entails.eval a c699 := derived699 a h
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c192 := h 191 (by decide)
  have h16 : Entails.eval a c240 := h 239 (by decide)
  have h17 : Entails.eval a c199 := h 198 (by decide)
  have h18 : Entails.eval a c111 := h 110 (by decide)
  have h19 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c629, some c698, some c93, some c91, some c30, some c700, some c245, some c32, some c99, some c585, some c508, some c282, some c699, some c22, some c240, some c415, some c233, some c477, some c594, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c547, c629, c698, c93, c91, c30, c700, c245, c32, c99, c585, c508, c282, c699, c22, c240, c415, c233, c477, c594] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c700 := derived700 a h
  have h7 : Entails.eval a c245 := h 244 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c585 := derived585 a h
  have h11 : Entails.eval a c508 := derived508 a h
  have h12 : Entails.eval a c282 := h 281 (by decide)
  have h13 : Entails.eval a c699 := derived699 a h
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c240 := h 239 (by decide)
  have h16 : Entails.eval a c415 := derived415 a h
  have h17 : Entails.eval a c233 := h 232 (by decide)
  have h18 : Entails.eval a c477 := derived477 a h
  have h19 : Entails.eval a c594 := derived594 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c93, some c4, some c22, some c91, some c30, some c547, some c585, some c147, some c699, some c5, some c106, some c52, some c700, some c508, some c245, some c32, some c99, some c701, some c109, some c641, some c181, some c280, some c594, some c111, some c221, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c629, c698, c93, c4, c22, c91, c30, c547, c585, c147, c699, c5, c106, c52, c700, c508, c245, c32, c99, c701, c109, c641, c181, c280, c594, c111, c221] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c547 := derived547 a h
  have h8 : Entails.eval a c585 := derived585 a h
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c699 := derived699 a h
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c700 := derived700 a h
  have h15 : Entails.eval a c508 := derived508 a h
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c99 := h 98 (by decide)
  have h19 : Entails.eval a c701 := derived701 a h
  have h20 : Entails.eval a c109 := h 108 (by decide)
  have h21 : Entails.eval a c641 := derived641 a h
  have h22 : Entails.eval a c181 := h 180 (by decide)
  have h23 : Entails.eval a c280 := h 279 (by decide)
  have h24 : Entails.eval a c594 := derived594 a h
  have h25 : Entails.eval a c111 := h 110 (by decide)
  have h26 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c702, some c629, some c698, some c93, some c91, some c30, some c547, some c601, some c200, some c32, some c99, some c594, some c221, some c587, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c702, c629, c698, c93, c91, c30, c547, c601, c200, c32, c99, c594, c221, c587] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c702 := derived702 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c601 := derived601 a h
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c594 := derived594 a h
  have h12 : Entails.eval a c221 := h 220 (by decide)
  have h13 : Entails.eval a c587 := derived587 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨33, by decide⟩, false), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c591, some c30, some c547, some c201, some c245, some c32, some c641, some c99, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c629, c698, c91, c93, c591, c30, c547, c201, c245, c32, c641, c99] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c591 := derived591 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c245 := h 244 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c641 := derived641 a h
  have h11 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c93, some c4, some c22, some c91, some c30, some c703, some c135, some c704, some c240, some c111, some c102, some c185, some c252, some c110, some c245, some c32, some c195, some c40, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c629, c698, c93, c4, c22, c91, c30, c703, c135, c704, c240, c111, c102, c185, c252, c110, c245, c32, c195, c40] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c703 := derived703 a h
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c704 := derived704 a h
  have h10 : Entails.eval a c240 := h 239 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c252 := h 251 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c32 := h 31 (by decide)
  have h18 : Entails.eval a c195 := h 194 (by decide)
  have h19 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c547, some c30, some c4, some c705, some c426, some c244, some c699, some c704, some c602, some c601, some c112, some c32, some c119, some c186, some c184, some c99, some c13, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c629, c698, c91, c93, c547, c30, c4, c705, c426, c244, c699, c704, c602, c601, c112, c32, c119, c186, c184, c99, c13] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c705 := derived705 a h
  have h8 : Entails.eval a c426 := derived426 a h
  have h9 : Entails.eval a c244 := h 243 (by decide)
  have h10 : Entails.eval a c699 := derived699 a h
  have h11 : Entails.eval a c704 := derived704 a h
  have h12 : Entails.eval a c602 := derived602 a h
  have h13 : Entails.eval a c601 := derived601 a h
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c32 := h 31 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  have h18 : Entails.eval a c184 := h 183 (by decide)
  have h19 : Entails.eval a c99 := h 98 (by decide)
  have h20 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c706, some c246, some c629, some c698, some c91, some c93, some c699, some c591, some c199, some c585, some c221, some c587, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c706, c246, c629, c698, c91, c93, c699, c591, c199, c585, c221, c587] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c698 := derived698 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c699 := derived699 a h
  have h7 : Entails.eval a c591 := derived591 a h
  have h8 : Entails.eval a c199 := h 198 (by decide)
  have h9 : Entails.eval a c585 := derived585 a h
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c587 := derived587 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c706, some c629, some c698, some c91, some c93, some c246, some c699, some c591, some c585, some c199, some c707, some c83, some c222, some c234, some c281, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c706, c629, c698, c91, c93, c246, c699, c591, c585, c199, c707, c83, c222, c234, c281] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c246 := h 245 (by decide)
  have h6 : Entails.eval a c699 := derived699 a h
  have h7 : Entails.eval a c591 := derived591 a h
  have h8 : Entails.eval a c585 := derived585 a h
  have h9 : Entails.eval a c199 := h 198 (by decide)
  have h10 : Entails.eval a c707 := derived707 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c222 := h 221 (by decide)
  have h13 : Entails.eval a c234 := h 233 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨37, by decide⟩, true), (⟨17, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c706, some c222, some c280, some c281, some c322, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c706, c222, c280, c281, c322] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c280 := h 279 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨17, by decide⟩, false), (⟨33, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c709, some c83, some c221, some c587, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c629, c698, c91, c93, c709, c83, c221, c587] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c709 := derived709 a h
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c587 := derived587 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨33, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c240, some c710, some c585, some c201, some c508, some c282, some c280, some c221, some c318, some c83, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c629, c698, c91, c93, c240, c710, c585, c201, c508, c282, c280, c221, c318, c83] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c240 := h 239 (by decide)
  have h5 : Entails.eval a c710 := derived710 a h
  have h6 : Entails.eval a c585 := derived585 a h
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c508 := derived508 a h
  have h9 : Entails.eval a c282 := h 281 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c318 := h 317 (by decide)
  have h13 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c708, some c629, some c698, some c91, some c93, some c711, some c199, some c200, some c508, some c585, some c282, some c280, some c316, some c318, some c83, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c708, c629, c698, c91, c93, c711, c199, c200, c508, c585, c282, c280, c316, c318, c83] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c708 := derived708 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c711 := derived711 a h
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c508 := derived508 a h
  have h9 : Entails.eval a c585 := derived585 a h
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c280 := h 279 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c318 := h 317 (by decide)
  have h14 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨11, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨33, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c134, some c144, some c111, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c134, c144, c111] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c134 := h 133 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c714 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨6, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f714 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c66, some c65, some c292, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p714 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked714 : lratChecker f714 p714 = .success := by decide +kernel
theorem unsat714 : Unsatisfiable (PosFin 57) f714 := by
  apply lratCheckerSound f714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p714
  · intro a ha; simp [p714] at ha; subst a; trivial
  · exact checked714
theorem derived714 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c714 := by
  apply localUnsat_implies_entails f714 [c629, c698, c91, c93, c66, c65, c292] c714 unsat714 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c715 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨52, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f715 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c712, some c591, some c708, some c706, some c714, some c713, some c12, some c13, some c186, some c180, some c110, some c508, some c245, some c282, some c641, some c236, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p715 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked715 : lratChecker f715 p715 = .success := by decide +kernel
theorem unsat715 : Unsatisfiable (PosFin 57) f715 := by
  apply lratCheckerSound f715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p715
  · intro a ha; simp [p715] at ha; subst a; trivial
  · exact checked715
theorem derived715 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c715 := by
  apply localUnsat_implies_entails f715 [c629, c698, c91, c93, c712, c591, c708, c706, c714, c713, c12, c13, c186, c180, c110, c508, c245, c282, c641, c236] c715 unsat715 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c708 := derived708 a h
  have h7 : Entails.eval a c706 := derived706 a h
  have h8 : Entails.eval a c714 := derived714 a h
  have h9 : Entails.eval a c713 := derived713 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c186 := h 185 (by decide)
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c508 := derived508 a h
  have h16 : Entails.eval a c245 := h 244 (by decide)
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c641 := derived641 a h
  have h19 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c716 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨7, by decide⟩, true), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f716 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c708, some c629, some c698, some c91, some c93, some c477, some c290, some c67, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p716 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked716 : lratChecker f716 p716 = .success := by decide +kernel
theorem unsat716 : Unsatisfiable (PosFin 57) f716 := by
  apply lratCheckerSound f716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p716
  · intro a ha; simp [p716] at ha; subst a; trivial
  · exact checked716
theorem derived716 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c716 := by
  apply localUnsat_implies_entails f716 [c712, c708, c629, c698, c91, c93, c477, c290, c67] c716 unsat716 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c708 := derived708 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c698 := derived698 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c477 := derived477 a h
  have h7 : Entails.eval a c290 := h 289 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c717 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨36, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨33, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f717 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c135, some c111, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p717 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked717 : lratChecker f717 p717 = .success := by decide +kernel
theorem unsat717 : Unsatisfiable (PosFin 57) f717 := by
  apply lratCheckerSound f717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p717
  · intro a ha; simp [p717] at ha; subst a; trivial
  · exact checked717
theorem derived717 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c717 := by
  apply localUnsat_implies_entails f717 [c147, c135, c111] c717 unsat717 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c718 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f718 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c708, some c706, some c629, some c698, some c91, some c93, some c716, some c65, some c717, some c12, some c14, some c178, some c111, some c102, some c188, some c252, some c41, some c126, some c122, some c109, some c220, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p718 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked718 : lratChecker f718 p718 = .success := by decide +kernel
theorem unsat718 : Unsatisfiable (PosFin 57) f718 := by
  apply lratCheckerSound f718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p718
  · intro a ha; simp [p718] at ha; subst a; trivial
  · exact checked718
theorem derived718 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c718 := by
  apply localUnsat_implies_entails f718 [c712, c708, c706, c629, c698, c91, c93, c716, c65, c717, c12, c14, c178, c111, c102, c188, c252, c41, c126, c122, c109, c220] c718 unsat718 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c708 := derived708 a h
  have h2 : Entails.eval a c706 := derived706 a h
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c698 := derived698 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c716 := derived716 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c717 := derived717 a h
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c178 := h 177 (by decide)
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c41 := h 40 (by decide)
  have h18 : Entails.eval a c126 := h 125 (by decide)
  have h19 : Entails.eval a c122 := h 121 (by decide)
  have h20 : Entails.eval a c109 := h 108 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c719 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f719 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c708, some c629, some c698, some c91, some c93, some c547, some c718, some c99, some c714, some c715, some c477, some c57, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p719 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked719 : lratChecker f719 p719 = .success := by decide +kernel
theorem unsat719 : Unsatisfiable (PosFin 57) f719 := by
  apply lratCheckerSound f719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p719
  · intro a ha; simp [p719] at ha; subst a; trivial
  · exact checked719
theorem derived719 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c719 := by
  apply localUnsat_implies_entails f719 [c712, c708, c629, c698, c91, c93, c547, c718, c99, c714, c715, c477, c57] c719 unsat719 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c708 := derived708 a h
  have h2 : Entails.eval a c629 := derived629 a h
  have h3 : Entails.eval a c698 := derived698 a h
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c547 := derived547 a h
  have h7 : Entails.eval a c718 := derived718 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c714 := derived714 a h
  have h10 : Entails.eval a c715 := derived715 a h
  have h11 : Entails.eval a c477 := derived477 a h
  have h12 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c720 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f720 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c712, some c591, some c245, some c201, some c547, some c57, some c67, some c412, some c99, some c282, some c289, some c323, some c232, some c84, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p720 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked720 : lratChecker f720 p720 = .success := by decide +kernel
theorem unsat720 : Unsatisfiable (PosFin 57) f720 := by
  apply lratCheckerSound f720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p720
  · intro a ha; simp [p720] at ha; subst a; trivial
  · exact checked720
theorem derived720 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c720 := by
  apply localUnsat_implies_entails f720 [c629, c698, c91, c93, c712, c591, c245, c201, c547, c57, c67, c412, c99, c282, c289, c323, c232, c84] c720 unsat720 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c547 := derived547 a h
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c67 := h 66 (by decide)
  have h11 : Entails.eval a c412 := derived412 a h
  have h12 : Entails.eval a c99 := h 98 (by decide)
  have h13 : Entails.eval a c282 := h 281 (by decide)
  have h14 : Entails.eval a c289 := h 288 (by decide)
  have h15 : Entails.eval a c323 := h 322 (by decide)
  have h16 : Entails.eval a c232 := h 231 (by decide)
  have h17 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c721 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, false), (⟨39, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f721 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c712, some c591, some c245, some c201, some c706, some c235, some c238, some c83, some c289, some c233, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p721 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked721 : lratChecker f721 p721 = .success := by decide +kernel
theorem unsat721 : Unsatisfiable (PosFin 57) f721 := by
  apply lratCheckerSound f721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p721
  · intro a ha; simp [p721] at ha; subst a; trivial
  · exact checked721
theorem derived721 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c721 := by
  apply localUnsat_implies_entails f721 [c629, c698, c91, c93, c712, c591, c245, c201, c706, c235, c238, c83, c289, c233] c721 unsat721 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c245 := h 244 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c706 := derived706 a h
  have h9 : Entails.eval a c235 := h 234 (by decide)
  have h10 : Entails.eval a c238 := h 237 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c289 := h 288 (by decide)
  have h13 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c722 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f722 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c712, some c591, some c708, some c706, some c206, some c245, some c201, some c720, some c292, some c205, some c721, some c59, some c288, some c94, some c236, some c487, some c85, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p722 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked722 : lratChecker f722 p722 = .success := by decide +kernel
theorem unsat722 : Unsatisfiable (PosFin 57) f722 := by
  apply lratCheckerSound f722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p722
  · intro a ha; simp [p722] at ha; subst a; trivial
  · exact checked722
theorem derived722 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c722 := by
  apply localUnsat_implies_entails f722 [c629, c698, c91, c93, c712, c591, c708, c706, c206, c245, c201, c720, c292, c205, c721, c59, c288, c94, c236, c487, c85] c722 unsat722 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c712 := derived712 a h
  have h5 : Entails.eval a c591 := derived591 a h
  have h6 : Entails.eval a c708 := derived708 a h
  have h7 : Entails.eval a c706 := derived706 a h
  have h8 : Entails.eval a c206 := h 205 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c720 := derived720 a h
  have h12 : Entails.eval a c292 := h 291 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c721 := derived721 a h
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c288 := h 287 (by decide)
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c236 := h 235 (by decide)
  have h19 : Entails.eval a c487 := derived487 a h
  have h20 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c723 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f723 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c712, some c708, some c706, some c629, some c698, some c91, some c93, some c719, some c722, some c290, some c294, some c714, some c205, some c94, some c247, some c657, some c111, some c110, some c185, some c183, some c12, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p723 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked723 : lratChecker f723 p723 = .success := by decide +kernel
theorem unsat723 : Unsatisfiable (PosFin 57) f723 := by
  apply lratCheckerSound f723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p723
  · intro a ha; simp [p723] at ha; subst a; trivial
  · exact checked723
theorem derived723 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c723 := by
  apply localUnsat_implies_entails f723 [c712, c708, c706, c629, c698, c91, c93, c719, c722, c290, c294, c714, c205, c94, c247, c657, c111, c110, c185, c183, c12] c723 unsat723 (by rfl) a
  have h0 : Entails.eval a c712 := derived712 a h
  have h1 : Entails.eval a c708 := derived708 a h
  have h2 : Entails.eval a c706 := derived706 a h
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c698 := derived698 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c719 := derived719 a h
  have h8 : Entails.eval a c722 := derived722 a h
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c294 := h 293 (by decide)
  have h11 : Entails.eval a c714 := derived714 a h
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  have h15 : Entails.eval a c657 := derived657 a h
  have h16 : Entails.eval a c111 := h 110 (by decide)
  have h17 : Entails.eval a c110 := h 109 (by decide)
  have h18 : Entails.eval a c185 := h 184 (by decide)
  have h19 : Entails.eval a c183 := h 182 (by decide)
  have h20 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c724 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f724 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c706, some c629, some c698, some c91, some c93, some c712, some c591, some c723, some c239, some c240, some c241, some c638, some c207, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p724 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked724 : lratChecker f724 p724 = .success := by decide +kernel
theorem unsat724 : Unsatisfiable (PosFin 57) f724 := by
  apply lratCheckerSound f724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p724
  · intro a ha; simp [p724] at ha; subst a; trivial
  · exact checked724
theorem derived724 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c724 := by
  apply localUnsat_implies_entails f724 [c706, c629, c698, c91, c93, c712, c591, c723, c239, c240, c241, c638, c207] c724 unsat724 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c629 := derived629 a h
  have h2 : Entails.eval a c698 := derived698 a h
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c712 := derived712 a h
  have h6 : Entails.eval a c591 := derived591 a h
  have h7 : Entails.eval a c723 := derived723 a h
  have h8 : Entails.eval a c239 := h 238 (by decide)
  have h9 : Entails.eval a c240 := h 239 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c638 := derived638 a h
  have h12 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c725 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨38, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f725 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c93, some c591, some c724, some c3, some c21, some c706, some c207, some c426, some c242, some c205, some c713, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p725 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked725 : lratChecker f725 p725 = .success := by decide +kernel
theorem unsat725 : Unsatisfiable (PosFin 57) f725 := by
  apply lratCheckerSound f725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p725
  · intro a ha; simp [p725] at ha; subst a; trivial
  · exact checked725
theorem derived725 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c725 := by
  apply localUnsat_implies_entails f725 [c629, c698, c91, c93, c591, c724, c3, c21, c706, c207, c426, c242, c205, c713] c725 unsat725 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c591 := derived591 a h
  have h5 : Entails.eval a c724 := derived724 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c706 := derived706 a h
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c426 := derived426 a h
  have h11 : Entails.eval a c242 := h 241 (by decide)
  have h12 : Entails.eval a c205 := h 204 (by decide)
  have h13 : Entails.eval a c713 := derived713 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c726 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f726 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c629, some c698, some c91, some c724, some c643, some c93, some c591, some c3, some c706, some c247, some c241, some c201, some c110, some c426, some c183, some c111, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p726 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked726 : lratChecker f726 p726 = .success := by decide +kernel
theorem unsat726 : Unsatisfiable (PosFin 57) f726 := by
  apply lratCheckerSound f726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p726
  · intro a ha; simp [p726] at ha; subst a; trivial
  · exact checked726
theorem derived726 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c726 := by
  apply localUnsat_implies_entails f726 [c629, c698, c91, c724, c643, c93, c591, c3, c706, c247, c241, c201, c110, c426, c183, c111] c726 unsat726 (by rfl) a
  have h0 : Entails.eval a c629 := derived629 a h
  have h1 : Entails.eval a c698 := derived698 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c724 := derived724 a h
  have h4 : Entails.eval a c643 := derived643 a h
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c591 := derived591 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c706 := derived706 a h
  have h9 : Entails.eval a c247 := h 246 (by decide)
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c426 := derived426 a h
  have h14 : Entails.eval a c183 := h 182 (by decide)
  have h15 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived726

end CochromaticTwenty.Certificates.B16_0_1
