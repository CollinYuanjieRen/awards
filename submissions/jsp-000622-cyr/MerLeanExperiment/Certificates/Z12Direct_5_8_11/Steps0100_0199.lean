import MerLeanExperiment.Certificates.Z12Direct_5_8_11.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_11-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_11
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c612 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c396, some c361, some c130, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p612 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 31) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c396, c361, c130] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c396 := h 395 (by decide)
  have h1 : Entails.eval a c361 := h 360 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c612, some c98, some c129, some c152, some c392, some c603, some c22, some c489, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p613 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 31) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c598, c612, c98, c129, c152, c392, c603, c22, c489] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c612 := derived612 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c129 := h 128 (by decide)
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c392 := h 391 (by decide)
  have h6 : Entails.eval a c603 := derived603 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c489 := h 488 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c613, some c605, some c98, some c213, some c75, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p614 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 31) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c598, c613, c605, c98, c213, c75] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c605 := derived605 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c599, some c601, some c598, some c565, some c611, some c608, some c614, some c32, some c607, some c144, some c376, some c83, some c6, some c45, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p615 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 31) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c599, c601, c598, c565, c611, c608, c614, c32, c607, c144, c376, c83, c6, c45] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c601 := derived601 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c565 := derived565 a h
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c608 := derived608 a h
  have h6 : Entails.eval a c614 := derived614 a h
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c607 := derived607 a h
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c376 := h 375 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c6 := h 5 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c599, some c601, some c598, some c565, some c605, some c144, some c376, some c83, some c208, some c245, some c247, some c45, some c290, some c200, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p616 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 31) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c599, c601, c598, c565, c605, c144, c376, c83, c208, c245, c247, c45, c290, c200] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c601 := derived601 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c565 := derived565 a h
  have h4 : Entails.eval a c605 := derived605 a h
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c376 := h 375 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c245 := h 244 (by decide)
  have h10 : Entails.eval a c247 := h 246 (by decide)
  have h11 : Entails.eval a c45 := h 44 (by decide)
  have h12 : Entails.eval a c290 := h 289 (by decide)
  have h13 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c616, some c98, some c82, some c75, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p617 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 31) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c598, c616, c98, c82, c75] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c616 := derived616 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c617, some c615, some c598, some c98, some c129, some c76, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p618 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 31) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c617, c615, c598, c98, c129, c76] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c617 := derived617 a h
  have h1 : Entails.eval a c615 := derived615 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c599, some c598, some c565, some c601, some c615, some c617, some c618, some c612, some c387, some c15, some c184, some c376, some c1, some c171, some c507, some c606, some c473, some c487, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p619 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 31) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c599, c598, c565, c601, c615, c617, c618, c612, c387, c15, c184, c376, c1, c171, c507, c606, c473, c487] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c599 := derived599 a h
  have h1 : Entails.eval a c598 := derived598 a h
  have h2 : Entails.eval a c565 := derived565 a h
  have h3 : Entails.eval a c601 := derived601 a h
  have h4 : Entails.eval a c615 := derived615 a h
  have h5 : Entails.eval a c617 := derived617 a h
  have h6 : Entails.eval a c618 := derived618 a h
  have h7 : Entails.eval a c612 := derived612 a h
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c184 := h 183 (by decide)
  have h11 : Entails.eval a c376 := h 375 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c507 := h 506 (by decide)
  have h15 : Entails.eval a c606 := derived606 a h
  have h16 : Entails.eval a c473 := h 472 (by decide)
  have h17 : Entails.eval a c487 := h 486 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨11, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c565, some c261, some c184, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p620 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 31) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c598, c565, c261, c184] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c599, some c565, some c76, some c122, some c34, some c620, some c479, some c22, some c164, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p621 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 31) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c619, c599, c565, c76, c122, c34, c620, c479, c22, c164] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c599 := derived599 a h
  have h2 : Entails.eval a c565 := derived565 a h
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c620 := derived620 a h
  have h7 : Entails.eval a c479 := h 478 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c599, some c598, some c565, some c621, some c32, some c13, some c438, some c447, some c479, some c54, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p622 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 31) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c619, c599, c598, c565, c621, c32, c13, c438, c447, c479, c54] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c599 := derived599 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c565 := derived565 a h
  have h4 : Entails.eval a c621 := derived621 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c438 := h 437 (by decide)
  have h8 : Entails.eval a c447 := h 446 (by decide)
  have h9 : Entails.eval a c479 := h 478 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c619, some c599, some c598, some c565, some c54, some c620, some c34, some c383, some c25, some c265, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p623 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 31) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c619, c599, c598, c565, c54, c620, c34, c383, c25, c265] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c599 := derived599 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c565 := derived565 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c620 := derived620 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c383 := h 382 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c622, some c53, some c619, some c599, some c565, some c623, some c405, some c44, some c476, some c130, some c138, some c336, some c335, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p624 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 31) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c598, c622, c53, c619, c599, c565, c623, c405, c44, c476, c130, c138, c336, c335] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c619 := derived619 a h
  have h4 : Entails.eval a c599 := derived599 a h
  have h5 : Entails.eval a c565 := derived565 a h
  have h6 : Entails.eval a c623 := derived623 a h
  have h7 : Entails.eval a c405 := h 404 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c476 := h 475 (by decide)
  have h10 : Entails.eval a c130 := h 129 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c336 := h 335 (by decide)
  have h13 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c622, some c624, some c98, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p625 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 31) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c598, c622, c624, c98] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c622 := derived622 a h
  have h2 : Entails.eval a c624 := derived624 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c625, some c47, some c619, some c599, some c565, some c98, some c170, some c623, some c15, some c44, some c190, some c237, some c283, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p626 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 31) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c598, c625, c47, c619, c599, c565, c98, c170, c623, c15, c44, c190, c237, c283] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c625 := derived625 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c619 := derived619 a h
  have h4 : Entails.eval a c599 := derived599 a h
  have h5 : Entails.eval a c565 := derived565 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c170 := h 169 (by decide)
  have h8 : Entails.eval a c623 := derived623 a h
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c565, some c599, some c619, some c625, some c47, some c626, some c75, some c82, some c121, some c623, some c34, some c22, some c190, some c266, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p627 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 31) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c598, c565, c599, c619, c625, c47, c626, c75, c82, c121, c623, c34, c22, c190, c266] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c599 := derived599 a h
  have h3 : Entails.eval a c619 := derived619 a h
  have h4 : Entails.eval a c625 := derived625 a h
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c626 := derived626 a h
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c623 := derived623 a h
  have h11 : Entails.eval a c34 := h 33 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c190 := h 189 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c565, some c67, some c75, some c121, some c34, some c38, some c620, some c22, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p628 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 31) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c627, c565, c67, c75, c121, c34, c38, c620, c22] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c620 := derived620 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c565, some c22, some c331, some c37, some c274, some c24, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p629 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 31) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c627, c565, c22, c331, c37, c274, c24] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c331 := h 330 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c598, some c565, some c629, some c38, some c34, some c334, some c37, some c274, some c25, some c44, some c309, some c182, some c100, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p630 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 31) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c627, c598, c565, c629, c38, c34, c334, c37, c274, c25, c44, c309, c182, c100] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c598 := derived598 a h
  have h2 : Entails.eval a c565 := derived565 a h
  have h3 : Entails.eval a c629 := derived629 a h
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c274 := h 273 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c309 := h 308 (by decide)
  have h12 : Entails.eval a c182 := h 181 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c598, some c565, some c630, some c54, some c620, some c34, some c37, some c231, some c25, some c274, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p631 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 31) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c627, c598, c565, c630, c54, c620, c34, c37, c231, c25, c274] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c598 := derived598 a h
  have h2 : Entails.eval a c565 := derived565 a h
  have h3 : Entails.eval a c630 := derived630 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c620 := derived620 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c628, some c598, some c631, some c69, some c166, some c13, some c168, some c73, some c119, some c369, some c412, some c66, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p632 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 31) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c628, c598, c631, c69, c166, c13, c168, c73, c119, c369, c412, c66] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c628 := derived628 a h
  have h1 : Entails.eval a c598 := derived598 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c168 := h 167 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c412 := h 411 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c632, some c146, some c628, some c598, some c69, some c166, some c61, some c13, some c168, some c73, some c119, some c487, some c486, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p633 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 31) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c627, c632, c146, c628, c598, c69, c166, c61, c13, c168, c73, c119, c487, c486] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c632 := derived632 a h
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c628 := derived628 a h
  have h4 : Entails.eval a c598 := derived598 a h
  have h5 : Entails.eval a c69 := h 68 (by decide)
  have h6 : Entails.eval a c166 := h 165 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c168 := h 167 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c487 := h 486 (by decide)
  have h13 : Entails.eval a c486 := h 485 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c627, some c565, some c632, some c146, some c633, some c34, some c38, some c620, some c22, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p634 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 31) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c627, c565, c632, c146, c633, c34, c38, c620, c22] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c565 := derived565 a h
  have h2 : Entails.eval a c632 := derived632 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c633 := derived633 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c620 := derived620 a h
  have h8 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c634, some c98, some c53, some c627, some c565, some c38, some c620, some c24, some c331, some c263, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p635 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 31) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c598, c634, c98, c53, c627, c565, c38, c620, c24, c331, c263] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c634 := derived634 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c627 := derived627 a h
  have h5 : Entails.eval a c565 := derived565 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c620 := derived620 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c331 := h 330 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c634, some c98, some c53, some c627, some c565, some c635, some c34, some c37, some c25, some c54, some c44, some c24, some c100, some c561, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p636 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 31) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c598, c634, c98, c53, c627, c565, c635, c34, c37, c25, c54, c44, c24, c100, c561] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c634 := derived634 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c627 := derived627 a h
  have h5 : Entails.eval a c565 := derived565 a h
  have h6 : Entails.eval a c635 := derived635 a h
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c100 := h 99 (by decide)
  have h14 : Entails.eval a c561 := derived561 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c598, some c627, some c634, some c53, some c98, some c636, some c67, some c69, some c166, some c117, some c13, some c168, some c203, some c73, some c119, some c401, some c410, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p637 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 31) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c598, c627, c634, c53, c98, c636, c67, c69, c166, c117, c13, c168, c203, c73, c119, c401, c410] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c598 := derived598 a h
  have h1 : Entails.eval a c627 := derived627 a h
  have h2 : Entails.eval a c634 := derived634 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c636 := derived636 a h
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c69 := h 68 (by decide)
  have h8 : Entails.eval a c166 := h 165 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c168 := h 167 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c401 := h 400 (by decide)
  have h16 : Entails.eval a c410 := h 409 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c36, some c151, some c226, some c269, some c23, some c288, some c255, some c468, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p638 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 31) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c637, c36, c151, c226, c269, c23, c288, c255, c468] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  have h4 : Entails.eval a c269 := h 268 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c288 := h 287 (by decide)
  have h7 : Entails.eval a c255 := h 254 (by decide)
  have h8 : Entails.eval a c468 := h 467 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨29, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c638, some c38, some c270, some c228, some c149, some c35, some c16, some c151, some c226, some c269, some c249, some c248, some c499, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p639 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 31) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c637, c638, c38, c270, c228, c149, c35, c16, c151, c226, c269, c249, c248, c499] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c638 := derived638 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c151 := h 150 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c249 := h 248 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c499 := h 498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c269, some c226, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p640 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 31) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c151, c269, c226] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c639, some c38, some c22, some c640, some c35, some c24, some c149, some c55, some c53, some c254, some c228, some c94, some c502, some c432, some c508, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p641 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 31) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c637, c639, c38, c22, c640, c35, c24, c149, c55, c53, c254, c228, c94, c502, c432, c508] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c640 := derived640 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c502 := h 501 (by decide)
  have h14 : Entails.eval a c432 := h 431 (by decide)
  have h15 : Entails.eval a c508 := h 507 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c639, some c641, some c36, some c151, some c640, some c42, some c23, some c22, some c138, some c137, some c272, some c463, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p642 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 31) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c637, c639, c641, c36, c151, c640, c42, c23, c22, c138, c137, c272, c463] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c639 := derived639 a h
  have h2 : Entails.eval a c641 := derived641 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c151 := h 150 (by decide)
  have h5 : Entails.eval a c640 := derived640 a h
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c137 := h 136 (by decide)
  have h11 : Entails.eval a c272 := h 271 (by decide)
  have h12 : Entails.eval a c463 := h 462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c642, some c151, some c640, some c42, some c22, some c147, some c124, some c123, some c109, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p643 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 31) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c642, c151, c640, c42, c22, c147, c124, c123, c109] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c642 := derived642 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c640 := derived640 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c123 := h 122 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c22, some c147, some c38, some c229, some c23, some c272, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p644 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 31) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c22, c147, c38, c229, c23, c272] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨12, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c147, some c38, some c229, some c148, some c310, some c272, some c325, some c346, some c123, some c475, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p645 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 31) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c637, c147, c38, c229, c148, c310, c272, c325, c346, c123, c475] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c310 := h 309 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c475 := h 474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c642, some c643, some c644, some c645, some c35, some c24, some c68, some c254, some c177, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p646 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 31) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c637, c642, c643, c644, c645, c35, c24, c68, c254, c177] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c642 := derived642 a h
  have h2 : Entails.eval a c643 := derived643 a h
  have h3 : Entails.eval a c644 := derived644 a h
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c646, some c642, some c640, some c645, some c35, some c68, some c70, some c524, some c158, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p647 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 31) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c637, c646, c642, c640, c645, c35, c68, c70, c524, c158] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c646 := derived646 a h
  have h2 : Entails.eval a c642 := derived642 a h
  have h3 : Entails.eval a c640 := derived640 a h
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c524 := derived524 a h
  have h9 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c68, some c70, some c524, some c158, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p648 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 31) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c68, c70, c524, c158] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c524 := derived524 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c648, some c158, some c339, some c173, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p649 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 31) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c648, c158, c339, c173] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c648 := derived648 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨28, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c35, some c99, some c105, some c411, some c358, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p650 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 31) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c637, c35, c99, c105, c411, c358] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c411 := h 410 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c648, some c650, some c339, some c649, some c172, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p651 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 31) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c648, c650, c339, c649, c172] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c648 := derived648 a h
  have h1 : Entails.eval a c650 := derived650 a h
  have h2 : Entails.eval a c339 := h 338 (by decide)
  have h3 : Entails.eval a c649 := derived649 a h
  have h4 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c642, some c646, some c647, some c651, some c147, some c38, some c229, some c23, some c272, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p652 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 31) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c642, c646, c647, c651, c147, c38, c229, c23, c272] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c642 := derived642 a h
  have h1 : Entails.eval a c646 := derived646 a h
  have h2 : Entails.eval a c647 := derived647 a h
  have h3 : Entails.eval a c651 := derived651 a h
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c229 := h 228 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c54, some c52, some c56, some c339, some c95, some c472, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p653 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 31) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c637, c54, c52, c56, c339, c95, c472] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c472 := h 471 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c652, some c653, some c23, some c43, some c45, some c40, some c103, some c107, some c21, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p654 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 31) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c652, c653, c23, c43, c45, c40, c103, c107, c21] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c652 := derived652 a h
  have h1 : Entails.eval a c653 := derived653 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c310, some c485, some c247, some c124, some c123, some c475, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p655 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 31) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c310, c485, c247, c124, c123, c475] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c310 := h 309 (by decide)
  have h1 : Entails.eval a c485 := h 484 (by decide)
  have h2 : Entails.eval a c247 := h 246 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c475 := h 474 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c655, some c155, some c230, some c273, some c45, some c284, some c177, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p656 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 31) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c655, c155, c230, c273, c45, c284, c177] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c230 := h 229 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c284 := h 283 (by decide)
  have h6 : Entails.eval a c177 := h 176 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c652, some c654, some c656, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p657 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 31) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c652, c654, c656] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c652 := derived652 a h
  have h1 : Entails.eval a c654 := derived654 a h
  have h2 : Entails.eval a c656 := derived656 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨10, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c657, some c547, some c105, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p658 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 31) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c657, c547, c105] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c657 := derived657 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c264, some c187, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p659 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 31) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c637, c264, c187] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c185, some c56, some c262, some c36, some c23, some c659, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p660 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 31) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c637, c185, c56, c262, c36, c23, c659] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c659 := derived659 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c368, some c186, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p661 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 31) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c637, c368, c186] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c661, some c196, some c315, some c203, some c234, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p662 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 31) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c661, c196, c315, c203, c234] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c661 := derived661 a h
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨15, by decide⟩, true), (⟨29, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c660, some c652, some c36, some c23, some c54, some c368, some c297, some c317, some c449, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p663 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 31) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c637, c660, c652, c36, c23, c54, c368, c297, c317, c449] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c660 := derived660 a h
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c368 := h 367 (by decide)
  have h7 : Entails.eval a c297 := h 296 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c449 := h 448 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨29, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c40, some c21, some c184, some c261, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p664 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 31) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c40, c21, c184, c261] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c652, some c658, some c660, some c664, some c663, some c661, some c196, some c203, some c234, some c503, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p665 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 31) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c652, c658, c660, c664, c663, c661, c196, c203, c234, c503] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c652 := derived652 a h
  have h1 : Entails.eval a c658 := derived658 a h
  have h2 : Entails.eval a c660 := derived660 a h
  have h3 : Entails.eval a c664 := derived664 a h
  have h4 : Entails.eval a c663 := derived663 a h
  have h5 : Entails.eval a c661 := derived661 a h
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c234 := h 233 (by decide)
  have h9 : Entails.eval a c503 := h 502 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨29, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c36, some c661, some c662, some c196, some c203, some c233, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p666 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 31) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c637, c36, c661, c662, c196, c203, c233] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c661 := derived661 a h
  have h3 : Entails.eval a c662 := derived662 a h
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c196, some c203, some c466, some c233, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p667 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 31) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c196, c203, c466, c233] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c466 := h 465 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c652, some c666, some c667, some c186, some c17, some c411, some c21, some c313, some c156, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p668 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 31) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c637, c652, c666, c667, c186, c17, c411, c21, c313, c156] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c652 := derived652 a h
  have h2 : Entails.eval a c666 := derived666 a h
  have h3 : Entails.eval a c667 := derived667 a h
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c411 := h 410 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c313 := h 312 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c186, some c411, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p669 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 31) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c637, c186, c411] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c411 := h 410 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c665, some c668, some c648, some c650, some c669, some c196, some c203, some c233, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p670 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 31) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c665, c668, c648, c650, c669, c196, c203, c233] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c668 := derived668 a h
  have h2 : Entails.eval a c648 := derived648 a h
  have h3 : Entails.eval a c650 := derived650 a h
  have h4 : Entails.eval a c669 := derived669 a h
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c35, some c504, some c189, some c317, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p671 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 31) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c637, c35, c504, c189, c317] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c504 := h 503 (by decide)
  have h3 : Entails.eval a c189 := h 188 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c665, some c670, some c651, some c663, some c285, some c291, some c233, some c671, some c89, some c125, some c490, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p672 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 31) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c665, c670, c651, c663, c285, c291, c233, c671, c89, c125, c490] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c665 := derived665 a h
  have h1 : Entails.eval a c670 := derived670 a h
  have h2 : Entails.eval a c651 := derived651 a h
  have h3 : Entails.eval a c663 := derived663 a h
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c671 := derived671 a h
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c490 := h 489 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c665, some c652, some c670, some c651, some c663, some c672, some c17, some c261, some c299, some c411, some c323, some c202, some c195, some c501, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p673 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 31) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c637, c665, c652, c670, c651, c663, c672, c17, c261, c299, c411, c323, c202, c195, c501] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c670 := derived670 a h
  have h4 : Entails.eval a c651 := derived651 a h
  have h5 : Entails.eval a c663 := derived663 a h
  have h6 : Entails.eval a c672 := derived672 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c411 := h 410 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c195 := h 194 (by decide)
  have h14 : Entails.eval a c501 := h 500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c665, some c673, some c660, some c648, some c651, some c35, some c659, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p674 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 31) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c637, c665, c673, c660, c648, c651, c35, c659] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c673 := derived673 a h
  have h3 : Entails.eval a c660 := derived660 a h
  have h4 : Entails.eval a c648 := derived648 a h
  have h5 : Entails.eval a c651 := derived651 a h
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c659 := derived659 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c55, some c187, some c48, some c196, some c203, some c13, some c81, some c87, some c86, some c8, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p675 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 31) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c637, c55, c187, c48, c196, c203, c13, c81, c87, c86, c8] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c190, some c24, some c428, some c123, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p676 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 31) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c637, c190, c24, c428, c123] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c428 := h 427 (by decide)
  have h4 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c187, some c19, some c675, some c659, some c55, some c24, some c268, some c488, some c338, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p677 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 31) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c637, c187, c19, c675, c659, c55, c24, c268, c488, c338] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c675 := derived675 a h
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c488 := h 487 (by decide)
  have h9 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c187, some c19, some c675, some c659, some c677, some c56, some c402, some c496, some c388, some c362, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p678 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 31) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c637, c187, c19, c675, c659, c677, c56, c402, c496, c388, c362] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c675 := derived675 a h
  have h4 : Entails.eval a c659 := derived659 a h
  have h5 : Entails.eval a c677 := derived677 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c402 := h 401 (by decide)
  have h8 : Entails.eval a c496 := h 495 (by decide)
  have h9 : Entails.eval a c388 := h 387 (by decide)
  have h10 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c56, some c402, some c5, some c346, some c362, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p679 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 31) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c637, c56, c402, c5, c346, c362] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c402 := h 401 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c675, some c659, some c55, some c187, some c19, some c678, some c679, some c24, some c268, some c36, some c338, some c123, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p680 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 31) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c637, c675, c659, c55, c187, c19, c678, c679, c24, c268, c36, c338, c123] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c675 := derived675 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c678 := derived678 a h
  have h7 : Entails.eval a c679 := derived679 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c338 := h 337 (by decide)
  have h12 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨1, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c680, some c675, some c659, some c55, some c24, some c428, some c676, some c488, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p681 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 31) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c637, c680, c675, c659, c55, c24, c428, c676, c488] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c680 := derived680 a h
  have h2 : Entails.eval a c675 := derived675 a h
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c428 := h 427 (by decide)
  have h7 : Entails.eval a c676 := derived676 a h
  have h8 : Entails.eval a c488 := h 487 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c675, some c659, some c55, some c680, some c681, some c56, some c402, some c191, some c384, some c88, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p682 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 31) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c637, c675, c659, c55, c680, c681, c56, c402, c191, c384, c88] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c675 := derived675 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c680 := derived680 a h
  have h5 : Entails.eval a c681 := derived681 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c402 := h 401 (by decide)
  have h8 : Entails.eval a c191 := h 190 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c187, some c682, some c18, some c675, some c659, some c55, some c56, some c198, some c25, some c105, some c286, some c337, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p683 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 31) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c637, c187, c682, c18, c675, c659, c55, c56, c198, c25, c105, c286, c337] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c682 := derived682 a h
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c675 := derived675 a h
  have h5 : Entails.eval a c659 := derived659 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c187, some c55, some c659, some c682, some c683, some c24, some c286, some c36, some c25, some c282, some c197, some c183, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p684 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 31) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c637, c187, c55, c659, c682, c683, c24, c286, c36, c25, c282, c197, c183] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c659 := derived659 a h
  have h4 : Entails.eval a c682 := derived682 a h
  have h5 : Entails.eval a c683 := derived683 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c286 := h 285 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c282 := h 281 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c279, some c24, some c684, some c44, some c42, some c348, some c566, some c238, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p685 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 31) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c637, c279, c24, c684, c44, c42, c348, c566, c238] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c279 := h 278 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c348 := h 347 (by decide)
  have h7 : Entails.eval a c566 := derived566 a h
  have h8 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c684, some c24, some c685, some c237, some c329, some c546, some c31, some c36, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p686 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 31) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c637, c684, c24, c685, c237, c329, c546, c31, c36] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c685 := derived685 a h
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c329 := h 328 (by decide)
  have h6 : Entails.eval a c546 := derived546 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c237, some c329, some c546, some c31, some c36, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p687 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 31) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c637, c237, c329, c546, c31, c36] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c237 := h 236 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  have h3 : Entails.eval a c546 := derived546 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c686, some c684, some c687, some c42, some c107, some c139, some c140, some c181, some c108, some c193, some c280, some c258, some c159, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p688 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 31) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c637, c686, c684, c687, c42, c107, c139, c140, c181, c108, c193, c280, c258, c159] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c684 := derived684 a h
  have h3 : Entails.eval a c687 := derived687 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c140 := h 139 (by decide)
  have h8 : Entails.eval a c181 := h 180 (by decide)
  have h9 : Entails.eval a c108 := h 107 (by decide)
  have h10 : Entails.eval a c193 := h 192 (by decide)
  have h11 : Entails.eval a c280 := h 279 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c684, some c686, some c688, some c22, some c35, some c283, some c258, some c329, some c206, some c348, some c212, some c130, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p689 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 31) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c637, c684, c686, c688, c22, c35, c283, c258, c329, c206, c348, c212, c130] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c686 := derived686 a h
  have h3 : Entails.eval a c688 := derived688 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c283 := h 282 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c329 := h 328 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c348 := h 347 (by decide)
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c689, some c684, some c22, some c283, some c37, some c267, some c39, some c224, some c303, some c430, some c18, some c240, some c431, some c132, some c10, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p690 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 31) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c689, c684, c22, c283, c37, c267, c39, c224, c303, c430, c18, c240, c431, c132, c10] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c689 := derived689 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c430 := h 429 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c240 := h 239 (by decide)
  have h12 : Entails.eval a c431 := h 430 (by decide)
  have h13 : Entails.eval a c132 := h 131 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c690, some c237, some c689, some c684, some c37, some c265, some c267, some c39, some c224, some c303, some c295, some c494, some c399, some c176, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p691 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 31) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c690, c237, c689, c684, c37, c265, c267, c39, c224, c303, c295, c494, c399, c176] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c237 := h 236 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c295 := h 294 (by decide)
  have h11 : Entails.eval a c494 := h 493 (by decide)
  have h12 : Entails.eval a c399 := h 398 (by decide)
  have h13 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c352, some c342, some c326, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p692 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 31) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c637, c352, c342, c326] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c342 := h 341 (by decide)
  have h3 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c285, some c692, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p693 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 31) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c285, c692] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c692 := derived692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c694 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c690, some c689, some c684, some c237, some c693, some c37, some c39, some c691, some c303, some c18, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p694 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 31) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c690, c689, c684, c237, c693, c37, c39, c691, c303, c18] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c690 := derived690 a h
  have h1 : Entails.eval a c689 := derived689 a h
  have h2 : Entails.eval a c684 := derived684 a h
  have h3 : Entails.eval a c237 := h 236 (by decide)
  have h4 : Entails.eval a c693 := derived693 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c691 := derived691 a h
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, false), (⟨22, by decide⟩, true), (⟨12, by decide⟩, false), (⟨16, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c37, some c39, some c240, some c423, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p695 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 31) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c637, c37, c39, c240, c423] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c423 := h 422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c684, some c689, some c690, some c694, some c42, some c695, some c285, some c344, some c38, some c40, some c423, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p696 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 31) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c637, c684, c689, c690, c694, c42, c695, c285, c344, c38, c40, c423] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c690 := derived690 a h
  have h4 : Entails.eval a c694 := derived694 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c695 := derived695 a h
  have h7 : Entails.eval a c285 := h 284 (by decide)
  have h8 : Entails.eval a c344 := h 343 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c423 := h 422 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c696, some c56, some c684, some c660, some c285, some c23, some c105, some c262, some c343, some c229, some c230, some c382, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p697 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 31) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c637, c696, c56, c684, c660, c285, c23, c105, c262, c343, c229, c230, c382] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c696 := derived696 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c660 := derived660 a h
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c230 := h 229 (by decide)
  have h12 : Entails.eval a c382 := h 381 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c301, some c382, some c281, some c236, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p698 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 31) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c637, c301, c382, c281, c236] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c382 := h 381 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨22, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c39, some c324, some c281, some c271, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p699 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 31) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c637, c39, c324, c281, c271] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c684, some c696, some c56, some c697, some c699, some c698, some c231, some c37, some c304, some c211, some c324, some c351, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p700 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 31) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c637, c684, c696, c56, c697, c699, c698, c231, c37, c304, c211, c324, c351] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c696 := derived696 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c697 := derived697 a h
  have h5 : Entails.eval a c699 := derived699 a h
  have h6 : Entails.eval a c698 := derived698 a h
  have h7 : Entails.eval a c231 := h 230 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c304 := h 303 (by decide)
  have h10 : Entails.eval a c211 := h 210 (by decide)
  have h11 : Entails.eval a c324 := h 323 (by decide)
  have h12 : Entails.eval a c351 := h 350 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c697, some c696, some c56, some c684, some c700, some c18, some c240, some c9, some c43, some c281, some c236, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p701 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 31) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c697, c696, c56, c684, c700, c18, c240, c9, c43, c281, c236] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c697 := derived697 a h
  have h1 : Entails.eval a c696 := derived696 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c700 := derived700 a h
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c240 := h 239 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c702 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨22, by decide⟩, false), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨1, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c18, some c240, some c43, some c66, some c64, some c212, some c241, some c110, some c483, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p702 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 31) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c637, c18, c240, c43, c66, c64, c212, c241, c110, c483] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c212 := h 211 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c483 := h 482 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c684, some c696, some c56, some c697, some c701, some c702, some c105, some c66, some c64, some c185, some c380, some c262, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p703 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 31) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c637, c684, c696, c56, c697, c701, c702, c105, c66, c64, c185, c380, c262] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c696 := derived696 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c697 := derived697 a h
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c702 := derived702 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c185 := h 184 (by decide)
  have h11 : Entails.eval a c380 := h 379 (by decide)
  have h12 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c696, some c56, some c684, some c703, some c43, some c697, some c701, some c702, some c380, some c110, some c262, some c353, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p704 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 31) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c637, c696, c56, c684, c703, c43, c697, c701, c702, c380, c110, c262, c353] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c696 := derived696 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c703 := derived703 a h
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c697 := derived697 a h
  have h7 : Entails.eval a c701 := derived701 a h
  have h8 : Entails.eval a c702 := derived702 a h
  have h9 : Entails.eval a c380 := h 379 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c262 := h 261 (by decide)
  have h12 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c696, some c56, some c684, some c703, some c43, some c697, some c704, some c139, some c267, some c224, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p705 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 31) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c637, c696, c56, c684, c703, c43, c697, c704, c139, c267, c224] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c696 := derived696 a h
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c684 := derived684 a h
  have h4 : Entails.eval a c703 := derived703 a h
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c697 := derived697 a h
  have h7 : Entails.eval a c704 := derived704 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c684, some c696, some c56, some c697, some c701, some c702, some c703, some c43, some c705, some c140, some c161, some c239, some c65, some c253, some c265, some c267, some c374, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p706 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 31) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c637, c684, c696, c56, c697, c701, c702, c703, c43, c705, c140, c161, c239, c65, c253, c265, c267, c374] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c684 := derived684 a h
  have h2 : Entails.eval a c696 := derived696 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c697 := derived697 a h
  have h5 : Entails.eval a c701 := derived701 a h
  have h6 : Entails.eval a c702 := derived702 a h
  have h7 : Entails.eval a c703 := derived703 a h
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c705 := derived705 a h
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c65 := h 64 (by decide)
  have h14 : Entails.eval a c253 := h 252 (by decide)
  have h15 : Entails.eval a c265 := h 264 (by decide)
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c374 := h 373 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨20, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c706, some c222, some c161, some c267, some c160, some c13, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p707 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 31) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c706, c222, c161, c267, c160, c13] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c222 := h 221 (by decide)
  have h2 : Entails.eval a c161 := h 160 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c706, some c13, some c140, some c707, some c221, some c65, some c684, some c457, some c492, some c57, some c12, some c320, some c467, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p708 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 31) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c637, c706, c13, c140, c707, c221, c65, c684, c457, c492, c57, c12, c320, c467] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c707 := derived707 a h
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c684 := derived684 a h
  have h8 : Entails.eval a c457 := h 456 (by decide)
  have h9 : Entails.eval a c492 := h 491 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  have h13 : Entails.eval a c467 := h 466 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, true), (⟨9, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c706, some c684, some c23, some c189, some c79, some c125, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p709 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 31) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c637, c706, c684, c23, c189, c79, c125] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c684 := derived684 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c189 := h 188 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c710 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c140, some c707, some c706, some c684, some c13, some c708, some c709, some c56, some c444, some c478, some c157, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p710 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 31) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c637, c140, c707, c706, c684, c13, c708, c709, c56, c444, c478, c157] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c707 := derived707 a h
  have h3 : Entails.eval a c706 := derived706 a h
  have h4 : Entails.eval a c684 := derived684 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c708 := derived708 a h
  have h7 : Entails.eval a c709 := derived709 a h
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c444 := h 443 (by decide)
  have h10 : Entails.eval a c478 := h 477 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c637, some c706, some c684, some c56, some c49, some c188, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p711 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 31) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c637, c706, c684, c56, c49, c188] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c637 := derived637 a h
  have h1 : Entails.eval a c706 := derived706 a h
  have h2 : Entails.eval a c684 := derived684 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived711

end CochromaticTwenty.Certificates.Z12Direct_5_8_11
