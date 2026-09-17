import MerLeanExperiment.Certificates.Z12Direct_5_3_13.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_3_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c605 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c595, some c70, some c53, some c604, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p605 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 31) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c557, c595, c70, c53, c604] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c604 := derived604 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c599, some c301, some c137, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p606 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 31) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c557, c599, c301, c137] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c599 := derived599 a h
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c557, some c595, some c603, some c145, some c605, some c606, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p607 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 31) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c557, c595, c603, c145, c605, c606] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c557 := derived557 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c603 := derived603 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c605 := derived605 a h
  have h5 : Entails.eval a c606 := derived606 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c588, some c595, some c599, some c409, some c382, some c70, some c65, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p608 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 31) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c588, c595, c599, c409, c382, c70, c65] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c588 := derived588 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c599 := derived599 a h
  have h3 : Entails.eval a c409 := derived409 a h
  have h4 : Entails.eval a c382 := h 381 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c588, some c594, some c287, some c608, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p609 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 31) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c588, c594, c287, c608] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c588 := derived588 a h
  have h1 : Entails.eval a c594 := derived594 a h
  have h2 : Entails.eval a c287 := h 286 (by decide)
  have h3 : Entails.eval a c608 := derived608 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c609, some c595, some c557, some c53, some c55, some c100, some c126, some c112, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p610 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 31) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c609, c595, c557, c53, c55, c100, c126, c112] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c609 := derived609 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c126 := h 125 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c599, some c491, some c588, some c595, some c557, some c70, some c251, some c53, some c610, some c378, some c52, some c603, some c607, some c110, some c217, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p611 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 31) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c599, c491, c588, c595, c557, c70, c251, c53, c610, c378, c52, c603, c607, c110, c217] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c491 := derived491 a h
  have h2 : Entails.eval a c588 := derived588 a h
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c557 := derived557 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c610 := derived610 a h
  have h9 : Entails.eval a c378 := h 377 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c603 := derived603 a h
  have h12 : Entails.eval a c607 := derived607 a h
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c611, some c588, some c491, some c67, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p612 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 31) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c611, c588, c491, c67] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c588 := derived588 a h
  have h2 : Entails.eval a c491 := derived491 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c612, some c595, some c557, some c52, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p613 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 31) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c612, c595, c557, c52] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c612 := derived612 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c603, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p614 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 31) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c613, c603] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c603 := derived603 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c615 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c613, some c607, some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p615 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 31) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c613, c607] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c613 := derived613 a h
  have h1 : Entails.eval a c607 := derived607 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c616 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c614, some c609, some c599, some c19, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p616 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 31) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c614, c609, c599, c19] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c614 := derived614 a h
  have h1 : Entails.eval a c609 := derived609 a h
  have h2 : Entails.eval a c599 := derived599 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c615, some c616, some c557, some c595, some c588, some c491, some c217]
def p617 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 31) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c615, c616, c557, c595, c588, c491, c217] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c615 := derived615 a h
  have h1 : Entails.eval a c616 := derived616 a h
  have h2 : Entails.eval a c557 := derived557 a h
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c588 := derived588 a h
  have h5 : Entails.eval a c491 := derived491 a h
  have h6 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived617

end CochromaticTwenty.Certificates.Z12Direct_5_3_13
