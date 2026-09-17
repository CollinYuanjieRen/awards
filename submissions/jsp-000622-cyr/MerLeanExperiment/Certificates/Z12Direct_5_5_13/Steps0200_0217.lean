import MerLeanExperiment.Certificates.Z12Direct_5_5_13.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_5_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c603 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c596, some c592, some c528, some c549, some c442, some c245, some c477, some c369, some c601, some c42, some c602, some c139, some c185, some c91, some c191, some c4, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p603 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 31) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c596, c592, c528, c549, c442, c245, c477, c369, c601, c42, c602, c139, c185, c91, c191, c4] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c596 := derived596 a h
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c528 := derived528 a h
  have h3 : Entails.eval a c549 := derived549 a h
  have h4 : Entails.eval a c442 := derived442 a h
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c477 := derived477 a h
  have h7 : Entails.eval a c369 := h 368 (by decide)
  have h8 : Entails.eval a c601 := derived601 a h
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c602 := derived602 a h
  have h11 : Entails.eval a c139 := h 138 (by decide)
  have h12 : Entails.eval a c185 := h 184 (by decide)
  have h13 : Entails.eval a c91 := h 90 (by decide)
  have h14 : Entails.eval a c191 := h 190 (by decide)
  have h15 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c603, some c549, some c597, some c368, some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p604 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 31) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c603, c549, c597, c368] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c549 := derived549 a h
  have h2 : Entails.eval a c597 := derived597 a h
  have h3 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c603, some c549, some c596, some c223, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p605 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 31) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c603, c549, c596, c223] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c549 := derived549 a h
  have h2 : Entails.eval a c596 := derived596 a h
  have h3 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c603, some c549, some c468, some c596, some c51, some c4, some c257, some c54, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p606 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 31) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c603, c549, c468, c596, c51, c4, c257, c54] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c549 := derived549 a h
  have h2 : Entails.eval a c468 := derived468 a h
  have h3 : Entails.eval a c596 := derived596 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c257 := h 256 (by decide)
  have h7 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c596, some c468, some c549, some c592, some c605, some c604, some c384, some c91, some c606, some c13, some c211, some c401, some c248, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p607 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 31) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c596, c468, c549, c592, c605, c604, c384, c91, c606, c13, c211, c401, c248] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c596 := derived596 a h
  have h1 : Entails.eval a c468 := derived468 a h
  have h2 : Entails.eval a c549 := derived549 a h
  have h3 : Entails.eval a c592 := derived592 a h
  have h4 : Entails.eval a c605 := derived605 a h
  have h5 : Entails.eval a c604 := derived604 a h
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c606 := derived606 a h
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c401 := h 400 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c604, some c603, some c549, some c596, some c468, some c363, some c388, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p608 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 31) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c604, c603, c549, c596, c468, c363, c388] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c604 := derived604 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c549 := derived549 a h
  have h3 : Entails.eval a c596 := derived596 a h
  have h4 : Entails.eval a c468 := derived468 a h
  have h5 : Entails.eval a c363 := h 362 (by decide)
  have h6 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c549, some c605, some c198, some c606, some c175, some c127, some c91, some c608, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p609 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 31) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c549, c605, c198, c606, c175, c127, c91, c608] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c549 := derived549 a h
  have h1 : Entails.eval a c605 := derived605 a h
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c606 := derived606 a h
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c608 := derived608 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c607, some c609, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p610 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 31) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c607, c609] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c607 := derived607 a h
  have h1 : Entails.eval a c609 := derived609 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c611 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c603, some c604, some c605, some c468, some c596, some c610, some c594, some c593, some c578, some c55, some c175, some c337, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p611 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 31) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c603, c604, c605, c468, c596, c610, c594, c593, c578, c55, c175, c337] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c603 := derived603 a h
  have h1 : Entails.eval a c604 := derived604 a h
  have h2 : Entails.eval a c605 := derived605 a h
  have h3 : Entails.eval a c468 := derived468 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c610 := derived610 a h
  have h6 : Entails.eval a c594 := derived594 a h
  have h7 : Entails.eval a c593 := derived593 a h
  have h8 : Entails.eval a c578 := derived578 a h
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c175 := h 174 (by decide)
  have h11 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c549, some c603, some c611, some c468, some c596, some c610, some c3, some c70, some c73, some c225, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p612 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 31) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c549, c603, c611, c468, c596, c610, c3, c70, c73, c225] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c549 := derived549 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c611 := derived611 a h
  have h3 : Entails.eval a c468 := derived468 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c610 := derived610 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c612, some c611, some c549, some c144, some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p613 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 31) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c612, c611, c549, c144] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c612 := derived612 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c549 := derived549 a h
  have h3 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c612, some c603, some c549, some c26, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p614 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 31) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c612, c603, c549, c26] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c612 := derived612 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c549 := derived549 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c596, some c610, some c605, some c604, some c578, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p615 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 31) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c613, c596, c610, c605, c604, c578] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c596 := derived596 a h
  have h2 : Entails.eval a c610 := derived610 a h
  have h3 : Entails.eval a c605 := derived605 a h
  have h4 : Entails.eval a c604 := derived604 a h
  have h5 : Entails.eval a c578 := derived578 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c615, some c612, some c29, some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p616 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 31) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c615, c612, c29] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c615 := derived615 a h
  have h1 : Entails.eval a c612 := derived612 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c615, some c611, some c605, some c165, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p617 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 31) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c615, c611, c605, c165] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c615 := derived615 a h
  have h1 : Entails.eval a c611 := derived611 a h
  have h2 : Entails.eval a c605 := derived605 a h
  have h3 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c549, some c603, some c604, some c468, some c596, some c616, some c617, some c376, some c334, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p618 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 31) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c549, c603, c604, c468, c596, c616, c617, c376, c334] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c549 := derived549 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c604 := derived604 a h
  have h3 : Entails.eval a c468 := derived468 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c616 := derived616 a h
  have h6 : Entails.eval a c617 := derived617 a h
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c334 := h 333 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c612, some c618, some c549, some c190, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p619 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 31) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c612, c618, c549, c190] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c612 := derived612 a h
  have h1 : Entails.eval a c618 := derived618 a h
  have h2 : Entails.eval a c549 := derived549 a h
  have h3 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c616, some c613, some c614, some c596, some c468, some c270]
def p620 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 31) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c619, c616, c613, c614, c596, c468, c270] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c616 := derived616 a h
  have h2 : Entails.eval a c613 := derived613 a h
  have h3 : Entails.eval a c614 := derived614 a h
  have h4 : Entails.eval a c596 := derived596 a h
  have h5 : Entails.eval a c468 := derived468 a h
  have h6 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived620

end CochromaticTwenty.Certificates.Z12Direct_5_5_13
