import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps0100_0199

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c614 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨20, by decide⟩, false), (⟨40, by decide⟩, false), (⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨23, by decide⟩, false), (⟨4, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c505, some c339, some c16, some c612, some c258, some c613, some c72, some c352, some c349, some c226, some c220, some c265, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c505, c339, c16, c612, c258, c613, c72, c352, c349, c226, c220, c265] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c612 := derived612 a h
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c613 := derived613 a h
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c352 := h 351 (by decide)
  have h8 : Entails.eval a c349 := h 348 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  have h10 : Entails.eval a c220 := h 219 (by decide)
  have h11 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨7, by decide⟩, false), (⟨51, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c105, some c94, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c112, c105, c94] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨17, by decide⟩, true), (⟨40, by decide⟩, false), (⟨16, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c1, some c156, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c57, c1, c156] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨35, by decide⟩, false), (⟨15, by decide⟩, true), (⟨40, by decide⟩, false), (⟨16, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c156, some c122, some c113, some c162, some c43, some c269, some c139, some c578, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c156, c122, c113, c162, c43, c269, c139, c578] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c156 := h 155 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c578 := derived578 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨2, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c43, some c42, some c145, some c210, some c45, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c43, c42, c145, c210, c45] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c210 := h 209 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c584, some c564, some c376, some c601, some c611, some c8, some c28, some c37, some c196, some c505, some c62, some c339, some c614, some c615, some c39, some c258, some c268, some c261, some c96, some c343, some c35, some c616, some c617, some c334, some c160, some c488, some c265, some c618, some c206, some c45, some c51, some c145, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c584, c564, c376, c601, c611, c8, c28, c37, c196, c505, c62, c339, c614, c615, c39, c258, c268, c261, c96, c343, c35, c616, c617, c334, c160, c488, c265, c618, c206, c45, c51, c145] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c584 := derived584 a h
  have h1 : Entails.eval a c564 := derived564 a h
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c601 := derived601 a h
  have h4 : Entails.eval a c611 := derived611 a h
  have h5 : Entails.eval a c8 := h 7 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c505 := derived505 a h
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  have h12 : Entails.eval a c614 := derived614 a h
  have h13 : Entails.eval a c615 := derived615 a h
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c261 := h 260 (by decide)
  have h18 : Entails.eval a c96 := h 95 (by decide)
  have h19 : Entails.eval a c343 := h 342 (by decide)
  have h20 : Entails.eval a c35 := h 34 (by decide)
  have h21 : Entails.eval a c616 := derived616 a h
  have h22 : Entails.eval a c617 := derived617 a h
  have h23 : Entails.eval a c334 := h 333 (by decide)
  have h24 : Entails.eval a c160 := h 159 (by decide)
  have h25 : Entails.eval a c488 := derived488 a h
  have h26 : Entails.eval a c265 := h 264 (by decide)
  have h27 : Entails.eval a c618 := derived618 a h
  have h28 : Entails.eval a c206 := h 205 (by decide)
  have h29 : Entails.eval a c45 := h 44 (by decide)
  have h30 : Entails.eval a c51 := h 50 (by decide)
  have h31 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c211, some c51, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c35, c211, c51] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨23, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c37, some c196, some c7, some c119, some c311, some c620, some c267, some c39, some c573, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c8, c37, c196, c7, c119, c311, c620, c267, c39, c573] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c196 := h 195 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c311 := h 310 (by decide)
  have h6 : Entails.eval a c620 := derived620 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c573 := derived573 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c564, some c311, some c573, some c215, some c102, some c309, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c564, c311, c573, c215, c102, c309] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c564 := derived564 a h
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c573 := derived573 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c564, some c107, some c622, some c119, some c196, some c131, some c194, some c197, some c204, some c102, some c10, some c112, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c564, c107, c622, c119, c196, c131, c194, c197, c204, c102, c10, c112] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c564 := derived564 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c622 := derived622 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  have h6 : Entails.eval a c194 := h 193 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨40, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c227, some c623, some c7, some c539, some c196, some c131, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c227, c623, c7, c539, c196, c131] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c227 := h 226 (by decide)
  have h1 : Entails.eval a c623 := derived623 a h
  have h2 : Entails.eval a c7 := h 6 (by decide)
  have h3 : Entails.eval a c539 := derived539 a h
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨21, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c7, some c27, some c267, some c196, some c223, some c127, some c163, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c36, c7, c27, c267, c196, c223, c127, c163] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c27 := h 26 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c191, some c204, some c615, some c18, some c102, some c256, some c426, some c24, some c165, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c62, c191, c204, c615, c18, c102, c256, c426, c24, c165] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c615 := derived615 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c426 := derived426 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c584, some c376, some c619, some c621, some c564, some c472, some c62, some c505, some c624, some c625, some c107, some c95, some c196, some c626, some c127, some c267, some c4, some c24, some c571, some c165, some c112, some c18, some c102, some c194, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c584, c376, c619, c621, c564, c472, c62, c505, c624, c625, c107, c95, c196, c626, c127, c267, c4, c24, c571, c165, c112, c18, c102, c194] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c584 := derived584 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c619 := derived619 a h
  have h3 : Entails.eval a c621 := derived621 a h
  have h4 : Entails.eval a c564 := derived564 a h
  have h5 : Entails.eval a c472 := derived472 a h
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c505 := derived505 a h
  have h8 : Entails.eval a c624 := derived624 a h
  have h9 : Entails.eval a c625 := derived625 a h
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c196 := h 195 (by decide)
  have h13 : Entails.eval a c626 := derived626 a h
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c4 := h 3 (by decide)
  have h17 : Entails.eval a c24 := h 23 (by decide)
  have h18 : Entails.eval a c571 := derived571 a h
  have h19 : Entails.eval a c165 := h 164 (by decide)
  have h20 : Entails.eval a c112 := h 111 (by decide)
  have h21 : Entails.eval a c18 := h 17 (by decide)
  have h22 : Entails.eval a c102 := h 101 (by decide)
  have h23 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c619, some c627, some c119, some c311, some c584, some c376, some c564, some c621, some c472, some c62, some c505, some c624, some c625, some c4, some c24, some c571, some c213, some c165, some c51, some c281, some c146, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c619, c627, c119, c311, c584, c376, c564, c621, c472, c62, c505, c624, c625, c4, c24, c571, c213, c165, c51, c281, c146] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c627 := derived627 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c564 := derived564 a h
  have h7 : Entails.eval a c621 := derived621 a h
  have h8 : Entails.eval a c472 := derived472 a h
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c505 := derived505 a h
  have h11 : Entails.eval a c624 := derived624 a h
  have h12 : Entails.eval a c625 := derived625 a h
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c571 := derived571 a h
  have h16 : Entails.eval a c213 := h 212 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c281 := h 280 (by decide)
  have h20 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c619, some c627, some c119, some c311, some c584, some c376, some c564, some c621, some c472, some c62, some c505, some c624, some c625, some c628, some c267, some c211, some c3, some c51, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c619, c627, c119, c311, c584, c376, c564, c621, c472, c62, c505, c624, c625, c628, c267, c211, c3, c51] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c619 := derived619 a h
  have h1 : Entails.eval a c627 := derived627 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c311 := h 310 (by decide)
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c564 := derived564 a h
  have h7 : Entails.eval a c621 := derived621 a h
  have h8 : Entails.eval a c472 := derived472 a h
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c505 := derived505 a h
  have h11 : Entails.eval a c624 := derived624 a h
  have h12 : Entails.eval a c625 := derived625 a h
  have h13 : Entails.eval a c628 := derived628 a h
  have h14 : Entails.eval a c267 := h 266 (by decide)
  have h15 : Entails.eval a c211 := h 210 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨52, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, false), (⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c256, some c211, some c102, some c306, some c615, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c267, c256, c211, c102, c306, c615] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c306 := h 305 (by decide)
  have h5 : Entails.eval a c615 := derived615 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c564, some c376, some c584, some c619, some c621, some c472, some c62, some c505, some c624, some c625, some c107, some c95, some c627, some c119, some c311, some c629, some c630, some c4, some c24, some c571, some c203, some c165, some c112, some c18, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c564, c376, c584, c619, c621, c472, c62, c505, c624, c625, c107, c95, c627, c119, c311, c629, c630, c4, c24, c571, c203, c165, c112, c18] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c564 := derived564 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c584 := derived584 a h
  have h3 : Entails.eval a c619 := derived619 a h
  have h4 : Entails.eval a c621 := derived621 a h
  have h5 : Entails.eval a c472 := derived472 a h
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c505 := derived505 a h
  have h8 : Entails.eval a c624 := derived624 a h
  have h9 : Entails.eval a c625 := derived625 a h
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c627 := derived627 a h
  have h13 : Entails.eval a c119 := h 118 (by decide)
  have h14 : Entails.eval a c311 := h 310 (by decide)
  have h15 : Entails.eval a c629 := derived629 a h
  have h16 : Entails.eval a c630 := derived630 a h
  have h17 : Entails.eval a c4 := h 3 (by decide)
  have h18 : Entails.eval a c24 := h 23 (by decide)
  have h19 : Entails.eval a c571 := derived571 a h
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c165 := h 164 (by decide)
  have h22 : Entails.eval a c112 := h 111 (by decide)
  have h23 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c505, some c4, some c24, some c350, some c165, some c334, some c6, some c262, some c266, some c31, some c221, some c107, some c105, some c346, some c75, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c505, c4, c24, c350, c165, c334, c6, c262, c266, c31, c221, c107, c105, c346, c75] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c4 := h 3 (by decide)
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c350 := h 349 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c221 := h 220 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c346 := h 345 (by decide)
  have h14 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c505, some c102, some c381, some c98, some c108, some c58, some c93, some c350, some c107, some c224, some c75, some c540, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c62, c505, c102, c381, c98, c108, c58, c93, c350, c107, c224, c75, c540] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c505 := derived505 a h
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c540 := derived540 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨12, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c14, some c266, some c191, some c200, some c125, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c6, c14, c266, c191, c200, c125] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c200 := h 199 (by decide)
  have h5 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨33, by decide⟩, false), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨21, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c634, some c154, some c10, some c1, some c133, some c203, some c229, some c137, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c634, c154, c10, c1, c133, c203, c229, c137] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c634 := derived634 a h
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c10 := h 9 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c229 := h 228 (by decide)
  have h7 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨27, by decide⟩, true), (⟨51, by decide⟩, false), (⟨32, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c191, some c147, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c196, c191, c147] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨21, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c311, some c631, some c260, some c564, some c376, some c62, some c632, some c633, some c111, some c105, some c615, some c54, some c57, some c306, some c636, some c128, some c634, some c635, some c165, some c271, some c224, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c311, c631, c260, c564, c376, c62, c632, c633, c111, c105, c615, c54, c57, c306, c636, c128, c634, c635, c165, c271, c224] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c260 := h 259 (by decide)
  have h3 : Entails.eval a c564 := derived564 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c632 := derived632 a h
  have h7 : Entails.eval a c633 := derived633 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c615 := derived615 a h
  have h11 : Entails.eval a c54 := h 53 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c306 := h 305 (by decide)
  have h14 : Entails.eval a c636 := derived636 a h
  have h15 : Entails.eval a c128 := h 127 (by decide)
  have h16 : Entails.eval a c634 := derived634 a h
  have h17 : Entails.eval a c635 := derived635 a h
  have h18 : Entails.eval a c165 := h 164 (by decide)
  have h19 : Entails.eval a c271 := h 270 (by decide)
  have h20 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c472, some c112, some c105, some c615, some c57, some c93, some c381, some c109, some c4, some c24, some c95, some c474, some c189, some c71, some c15, some c10, some c156, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c472, c112, c105, c615, c57, c93, c381, c109, c4, c24, c95, c474, c189, c71, c15, c10, c156] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c472 := derived472 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c615 := derived615 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c381 := h 380 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c474 := derived474 a h
  have h12 : Entails.eval a c189 := h 188 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c10 := h 9 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨38, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c31, some c346, some c262, some c228, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c57, c31, c346, c262, c228] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c346 := h 345 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨25, by decide⟩, true), (⟨16, by decide⟩, false), (⟨36, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨21, by decide⟩, false), (⟨31, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c164, some c350, some c158, some c125, some c266, some c132, some c228, some c198, some c282, some c113, some c133, some c137, some c229, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c164, c350, c158, c125, c266, c132, c228, c198, c282, c113, c133, c137, c229] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c164 := h 163 (by decide)
  have h1 : Entails.eval a c350 := h 349 (by decide)
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c125 := h 124 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨36, by decide⟩, false), (⟨12, by decide⟩, false), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c334, some c346, some c221, some c266, some c132, some c228, some c165, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c334, c346, c221, c266, c132, c228, c165] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c334 := h 333 (by decide)
  have h1 : Entails.eval a c346 := h 345 (by decide)
  have h2 : Entails.eval a c221 := h 220 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨21, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c637, some c638, some c472, some c311, some c631, some c260, some c381, some c306, some c96, some c61, some c636, some c109, some c128, some c24, some c164, some c19, some c641, some c350, some c640, some c639, some c43, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c376, c637, c638, c472, c311, c631, c260, c381, c306, c96, c61, c636, c109, c128, c24, c164, c19, c641, c350, c640, c639, c43] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c637 := derived637 a h
  have h2 : Entails.eval a c638 := derived638 a h
  have h3 : Entails.eval a c472 := derived472 a h
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c61 := h 60 (by decide)
  have h11 : Entails.eval a c636 := derived636 a h
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c128 := h 127 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c164 := h 163 (by decide)
  have h16 : Entails.eval a c19 := h 18 (by decide)
  have h17 : Entails.eval a c641 := derived641 a h
  have h18 : Entails.eval a c350 := h 349 (by decide)
  have h19 : Entails.eval a c640 := derived640 a h
  have h20 : Entails.eval a c639 := derived639 a h
  have h21 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c472, some c631, some c260, some c564, some c96, some c61, some c109, some c4, some c24, some c474, some c164, some c339, some c19, some c350, some c196, some c641, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c376, c472, c631, c260, c564, c96, c61, c109, c4, c24, c474, c164, c339, c19, c350, c196, c641] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c472 := derived472 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c564 := derived564 a h
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c474 := derived474 a h
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c339 := h 338 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  have h16 : Entails.eval a c641 := derived641 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c472, some c631, some c260, some c505, some c75, some c540, some c224, some c350, some c58, some c109, some c4, some c164, some c641, some c19, some c196, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c376, c472, c631, c260, c505, c75, c540, c224, c350, c58, c109, c4, c164, c641, c19, c196] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c472 := derived472 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c505 := derived505 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c540 := derived540 a h
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c109 := h 108 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c164 := h 163 (by decide)
  have h13 : Entails.eval a c641 := derived641 a h
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c540, some c352, some c224, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c540, c352, c224] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c540 := derived540 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨52, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true), (⟨40, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c160, some c128, some c12, some c192, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c196, c160, c128, c12, c192] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c12 := h 11 (by decide)
  have h4 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨51, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c472, some c631, some c260, some c564, some c644, some c339, some c645, some c75, some c643, some c309, some c311, some c24, some c224, some c109, some c348, some c279, some c58, some c457, some c646, some c140, some c151, some c147, some c333, some c327, some c194, some c157, some c173, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c376, c472, c631, c260, c564, c644, c339, c645, c75, c643, c309, c311, c24, c224, c109, c348, c279, c58, c457, c646, c140, c151, c147, c333, c327, c194, c157, c173] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c472 := derived472 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c564 := derived564 a h
  have h5 : Entails.eval a c644 := derived644 a h
  have h6 : Entails.eval a c339 := h 338 (by decide)
  have h7 : Entails.eval a c645 := derived645 a h
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c643 := derived643 a h
  have h10 : Entails.eval a c309 := h 308 (by decide)
  have h11 : Entails.eval a c311 := h 310 (by decide)
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c109 := h 108 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c279 := h 278 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c457 := derived457 a h
  have h19 : Entails.eval a c646 := derived646 a h
  have h20 : Entails.eval a c140 := h 139 (by decide)
  have h21 : Entails.eval a c151 := h 150 (by decide)
  have h22 : Entails.eval a c147 := h 146 (by decide)
  have h23 : Entails.eval a c333 := h 332 (by decide)
  have h24 : Entails.eval a c327 := h 326 (by decide)
  have h25 : Entails.eval a c194 := h 193 (by decide)
  have h26 : Entails.eval a c157 := h 156 (by decide)
  have h27 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c260, some c564, some c376, some c637, some c472, some c638, some c642, some c644, some c339, some c645, some c75, some c647, some c349, some c334, some c348, some c228, some c221, some c266, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c631, c260, c564, c376, c637, c472, c638, c642, c644, c339, c645, c75, c647, c349, c334, c348, c228, c221, c266] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c564 := derived564 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c637 := derived637 a h
  have h5 : Entails.eval a c472 := derived472 a h
  have h6 : Entails.eval a c638 := derived638 a h
  have h7 : Entails.eval a c642 := derived642 a h
  have h8 : Entails.eval a c644 := derived644 a h
  have h9 : Entails.eval a c339 := h 338 (by decide)
  have h10 : Entails.eval a c645 := derived645 a h
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c647 := derived647 a h
  have h13 : Entails.eval a c349 := h 348 (by decide)
  have h14 : Entails.eval a c334 := h 333 (by decide)
  have h15 : Entails.eval a c348 := h 347 (by decide)
  have h16 : Entails.eval a c228 := h 227 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c260, some c564, some c376, some c615, some c5, some c25, some c540, some c645, some c224, some c339, some c164, some c644, some c4, some c633, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c631, c260, c564, c376, c615, c5, c25, c540, c645, c224, c339, c164, c644, c4, c633] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c564 := derived564 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c615 := derived615 a h
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c540 := derived540 a h
  have h8 : Entails.eval a c645 := derived645 a h
  have h9 : Entails.eval a c224 := h 223 (by decide)
  have h10 : Entails.eval a c339 := h 338 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  have h12 : Entails.eval a c644 := derived644 a h
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c633 := derived633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨12, by decide⟩, false), (⟨53, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c25, some c102, some c96, some c164, some c109, some c24, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c5, c25, c102, c96, c164, c109, c24] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c260, some c564, some c376, some c311, some c648, some c649, some c381, some c306, some c636, some c128, some c650, some c112, some c105, some c54, some c638, some c57, some c117, some c62, some c634, some c203, some c154, some c10, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c631, c260, c564, c376, c311, c648, c649, c381, c306, c636, c128, c650, c112, c105, c54, c638, c57, c117, c62, c634, c203, c154, c10] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c564 := derived564 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c311 := h 310 (by decide)
  have h5 : Entails.eval a c648 := derived648 a h
  have h6 : Entails.eval a c649 := derived649 a h
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c306 := h 305 (by decide)
  have h9 : Entails.eval a c636 := derived636 a h
  have h10 : Entails.eval a c128 := h 127 (by decide)
  have h11 : Entails.eval a c650 := derived650 a h
  have h12 : Entails.eval a c112 := h 111 (by decide)
  have h13 : Entails.eval a c105 := h 104 (by decide)
  have h14 : Entails.eval a c54 := h 53 (by decide)
  have h15 : Entails.eval a c638 := derived638 a h
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c117 := h 116 (by decide)
  have h18 : Entails.eval a c62 := h 61 (by decide)
  have h19 : Entails.eval a c634 := derived634 a h
  have h20 : Entails.eval a c203 := h 202 (by decide)
  have h21 : Entails.eval a c154 := h 153 (by decide)
  have h22 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c112, some c105, some c638, some c57, some c10, some c62, some c14, some c154, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c112, c105, c638, c57, c10, c62, c14, c154] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c638 := derived638 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  have h7 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨16, by decide⟩, true), (⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c191, some c652, some c102, some c96, some c61, some c472, some c109, some c19, some c4, some c24, some c164, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c381, c191, c652, c102, c96, c61, c472, c109, c19, c4, c24, c164] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c191 := h 190 (by decide)
  have h2 : Entails.eval a c652 := derived652 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c472 := derived472 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c376, some c472, some c643, some c19, some c194, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c196, c376, c472, c643, c19, c194] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c472 := derived472 a h
  have h3 : Entails.eval a c643 := derived643 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c260, some c564, some c376, some c651, some c119, some c196, some c653, some c615, some c654, some c62, some c633, some c632, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c631, c260, c564, c376, c651, c119, c196, c653, c615, c654, c62, c633, c632] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c564 := derived564 a h
  have h3 : Entails.eval a c376 := h 375 (by decide)
  have h4 : Entails.eval a c651 := derived651 a h
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c653 := derived653 a h
  have h8 : Entails.eval a c615 := derived615 a h
  have h9 : Entails.eval a c654 := derived654 a h
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c633 := derived633 a h
  have h12 : Entails.eval a c632 := derived632 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨53, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c615, some c655, some c196, some c194, some c5, some c19, some c256, some c107, some c438, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c376, c615, c655, c196, c194, c5, c19, c256, c107, c438] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c615 := derived615 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c438 := derived438 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c57, some c93, some c438, some c108, some c256, some c11, some c25, some c153, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c57, c93, c438, c108, c256, c11, c25, c153] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c57 := h 56 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c438 := derived438 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨25, by decide⟩, true), (⟨37, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c153, some c113, some c133, some c232, some c320, some c295, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c153, c113, c133, c232, c320, c295] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c153 := h 152 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨8, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c505, some c75, some c334, some c335, some c457, some c350, some c162, some c256, some c73, some c115, some c108, some c264, some c32, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c505, c75, c334, c335, c457, c350, c162, c256, c73, c115, c108, c264, c32] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c505 := derived505 a h
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c334 := h 333 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c457 := derived457 a h
  have h5 : Entails.eval a c350 := h 349 (by decide)
  have h6 : Entails.eval a c162 := h 161 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c108 := h 107 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c438, some c657, some c192, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c438, c657, c192] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c438 := derived438 a h
  have h1 : Entails.eval a c657 := derived657 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨3, by decide⟩, false), (⟨38, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c505, some c615, some c660, some c107, some c43, some c75, some c659, some c658, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c51, c505, c615, c660, c107, c43, c75, c659, c658] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c505 := derived505 a h
  have h2 : Entails.eval a c615 := derived615 a h
  have h3 : Entails.eval a c660 := derived660 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c658 := derived658 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c615, some c655, some c631, some c260, some c564, some c62, some c98, some c102, some c505, some c656, some c119, some c311, some c309, some c661, some c5, some c137, some c256, some c438, some c443, some c457, some c107, some c320, some c75, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c376, c615, c655, c631, c260, c564, c62, c98, c102, c505, c656, c119, c311, c309, c661, c5, c137, c256, c438, c443, c457, c107, c320, c75] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c615 := derived615 a h
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c564 := derived564 a h
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c505 := derived505 a h
  have h10 : Entails.eval a c656 := derived656 a h
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c311 := h 310 (by decide)
  have h13 : Entails.eval a c309 := h 308 (by decide)
  have h14 : Entails.eval a c661 := derived661 a h
  have h15 : Entails.eval a c5 := h 4 (by decide)
  have h16 : Entails.eval a c137 := h 136 (by decide)
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c438 := derived438 a h
  have h19 : Entails.eval a c443 := derived443 a h
  have h20 : Entails.eval a c457 := derived457 a h
  have h21 : Entails.eval a c107 := h 106 (by decide)
  have h22 : Entails.eval a c320 := h 319 (by decide)
  have h23 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨31, by decide⟩, false), (⟨15, by decide⟩, true), (⟨13, by decide⟩, true), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c615, some c472, some c19, some c5, some c256, some c309, some c438, some c443, some c137, some c43, some c79, some c78, some c229, some c180, some c113, some c198, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c615, c472, c19, c5, c256, c309, c438, c443, c137, c43, c79, c78, c229, c180, c113, c198] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c615 := derived615 a h
  have h1 : Entails.eval a c472 := derived472 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c438 := derived438 a h
  have h7 : Entails.eval a c443 := derived443 a h
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c180 := h 179 (by decide)
  have h14 : Entails.eval a c113 := h 112 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c443, some c457, some c320, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c443, c457, c320] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c443 := derived443 a h
  have h1 : Entails.eval a c457 := derived457 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨45, by decide⟩, false), (⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c320, some c359, some c335, some c328, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c78, c320, c359, c335, c328] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨37, by decide⟩, false), (⟨2, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c433, some c665, some c354, some c133, some c83, some c198, some c180, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c433, c665, c354, c133, c83, c198, c180] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c665 := derived665 a h
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c133 := h 132 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c198 := h 197 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨2, by decide⟩, false), (⟨53, by decide⟩, true), (⟨6, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c357, some c363, some c83, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c357, c363, c83] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c357 := h 356 (by decide)
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨2, by decide⟩, false), (⟨31, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c43, some c666, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c43, c666] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨49, by decide⟩, true), (⟨2, by decide⟩, false), (⟨31, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c668, some c57, some c94, some c320, some c354, some c355, some c81, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c668, c57, c94, c320, c354, c355, c81] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c668 := derived668 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c376, some c662, some c472, some c615, some c655, some c631, some c260, some c564, some c19, some c196, some c119, some c663, some c96, some c61, some c667, some c669, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c376, c662, c472, c615, c655, c631, c260, c564, c19, c196, c119, c663, c96, c61, c667, c669] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c376 := h 375 (by decide)
  have h1 : Entails.eval a c662 := derived662 a h
  have h2 : Entails.eval a c472 := derived472 a h
  have h3 : Entails.eval a c615 := derived615 a h
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c564 := derived564 a h
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c663 := derived663 a h
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c667 := derived667 a h
  have h15 : Entails.eval a c669 := derived669 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c664, some c433, some c93, some c96, some c665, some c256, some c192, some c354, some c32, some c176, some c234, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c664, c433, c93, c96, c665, c256, c192, c354, c32, c176, c234] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c664 := derived664 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c665 := derived665 a h
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c176 := h 175 (by decide)
  have h10 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨51, by decide⟩, true), (⟨20, by decide⟩, false), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c472, some c615, some c671, some c109, some c669, some c17, some c203, some c15, some c147, some c51, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c472, c615, c671, c109, c669, c17, c203, c15, c147, c51] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c472 := derived472 a h
  have h1 : Entails.eval a c615 := derived615 a h
  have h2 : Entails.eval a c671 := derived671 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c669 := derived669 a h
  have h5 : Entails.eval a c17 := h 16 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c670, some c376, some c662, some c472, some c655, some c564, some c311, some c672, some c196, some c204, some c15, some c147, some c51, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c670, c376, c662, c472, c655, c564, c311, c672, c196, c204, c15, c147, c51] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c670 := derived670 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c662 := derived662 a h
  have h3 : Entails.eval a c472 := derived472 a h
  have h4 : Entails.eval a c655 := derived655 a h
  have h5 : Entails.eval a c564 := derived564 a h
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c672 := derived672 a h
  have h8 : Entails.eval a c196 := h 195 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c670, some c376, some c662, some c472, some c615, some c631, some c260, some c564, some c540, some c673, some c119, some c196, some c194, some c197, some c204, some c96, some c109, some c526, some c505, some c339, some c228, some c328, some c262, some c359, some c170, some c1, some c78, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c670, c376, c662, c472, c615, c631, c260, c564, c540, c673, c119, c196, c194, c197, c204, c96, c109, c526, c505, c339, c228, c328, c262, c359, c170, c1, c78] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c670 := derived670 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c662 := derived662 a h
  have h3 : Entails.eval a c472 := derived472 a h
  have h4 : Entails.eval a c615 := derived615 a h
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c260 := h 259 (by decide)
  have h7 : Entails.eval a c564 := derived564 a h
  have h8 : Entails.eval a c540 := derived540 a h
  have h9 : Entails.eval a c673 := derived673 a h
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c194 := h 193 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c526 := derived526 a h
  have h18 : Entails.eval a c505 := derived505 a h
  have h19 : Entails.eval a c339 := h 338 (by decide)
  have h20 : Entails.eval a c228 := h 227 (by decide)
  have h21 : Entails.eval a c328 := h 327 (by decide)
  have h22 : Entails.eval a c262 := h 261 (by decide)
  have h23 : Entails.eval a c359 := h 358 (by decide)
  have h24 : Entails.eval a c170 := h 169 (by decide)
  have h25 : Entails.eval a c1 := h 0 (by decide)
  have h26 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c670, some c376, some c615, some c655, some c631, some c260, some c433, some c674, some c25, some c61, some c267, some c240, some c656, some c176, some c119, some c203, some c3, some c115, some c51, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c670, c376, c615, c655, c631, c260, c433, c674, c25, c61, c267, c240, c656, c176, c119, c203, c3, c115, c51] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c670 := derived670 a h
  have h1 : Entails.eval a c376 := h 375 (by decide)
  have h2 : Entails.eval a c615 := derived615 a h
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c433 := derived433 a h
  have h7 : Entails.eval a c674 := derived674 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c240 := h 239 (by decide)
  have h12 : Entails.eval a c656 := derived656 a h
  have h13 : Entails.eval a c176 := h 175 (by decide)
  have h14 : Entails.eval a c119 := h 118 (by decide)
  have h15 : Entails.eval a c203 := h 202 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c115 := h 114 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨37, by decide⟩, true), (⟨45, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c260, some c376, some c655, some c615, some c662, some c25, some c61, some c472, some c656, some c256, some c75, some c119, some c443, some c457, some c311, some c309, some c323, some c295, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c631, c260, c376, c655, c615, c662, c25, c61, c472, c656, c256, c75, c119, c443, c457, c311, c309, c323, c295] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c376 := h 375 (by decide)
  have h3 : Entails.eval a c655 := derived655 a h
  have h4 : Entails.eval a c615 := derived615 a h
  have h5 : Entails.eval a c662 := derived662 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c61 := h 60 (by decide)
  have h8 : Entails.eval a c472 := derived472 a h
  have h9 : Entails.eval a c656 := derived656 a h
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c443 := derived443 a h
  have h14 : Entails.eval a c457 := derived457 a h
  have h15 : Entails.eval a c311 := h 310 (by decide)
  have h16 : Entails.eval a c309 := h 308 (by decide)
  have h17 : Entails.eval a c323 := h 322 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause ((⟨17, by decide⟩, false) :: (⟨1, by decide⟩, true) :: (⟨56, by decide⟩, false) :: (⟨4, by decide⟩, false) :: (⟨5, by decide⟩, true) :: (⟨6, by decide⟩, true) :: (⟨3, by decide⟩, false) :: (⟨7, by decide⟩, false) :: (⟨8, by decide⟩, false) :: (⟨10, by decide⟩, false) :: (⟨2, by decide⟩, true) :: (⟨9, by decide⟩, true) :: (⟨11, by decide⟩, false) :: (⟨13, by decide⟩, true) :: (⟨15, by decide⟩, false) :: (⟨16, by decide⟩, true) :: (⟨12, by decide⟩, true) :: (⟨18, by decide⟩, false) :: (⟨19, by decide⟩, true) :: (⟨20, by decide⟩, false) :: (⟨21, by decide⟩, false) :: (⟨22, by decide⟩, true) :: (⟨23, by decide⟩, true) :: (⟨24, by decide⟩, true) :: (⟨25, by decide⟩, true) :: (⟨26, by decide⟩, true) :: (⟨27, by decide⟩, true) :: (⟨28, by decide⟩, false) :: (⟨14, by decide⟩, false) :: (⟨30, by decide⟩, false) :: (⟨31, by decide⟩, true) :: (⟨32, by decide⟩, false) :: (⟨33, by decide⟩, false) :: (⟨34, by decide⟩, true) :: (⟨35, by decide⟩, false) :: (⟨36, by decide⟩, true) :: (⟨37, by decide⟩, false) :: (⟨38, by decide⟩, false) :: (⟨39, by decide⟩, true) :: (⟨40, by decide⟩, true) :: (⟨41, by decide⟩, false) :: (⟨42, by decide⟩, false) :: (⟨43, by decide⟩, false) :: (⟨44, by decide⟩, true) :: (⟨45, by decide⟩, true) :: (⟨46, by decide⟩, true) :: (⟨47, by decide⟩, true) :: (⟨48, by decide⟩, false) :: (⟨49, by decide⟩, true) :: (⟨50, by decide⟩, false) :: (⟨51, by decide⟩, true) :: (⟨52, by decide⟩, true) :: (⟨53, by decide⟩, false) :: (⟨54, by decide⟩, true) :: (⟨55, by decide⟩, false) :: []) (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c137, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c385, c137] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨53, by decide⟩, false), (⟨52, by decide⟩, false), (⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨31, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c127, some c131, some c303, some c203, some c129, some c148, some c250, some c307, some c208, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c120, c127, c131, c303, c203, c129, c148, c250, c307, c208] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c127 := h 126 (by decide)
  have h2 : Entails.eval a c131 := h 130 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c129 := h 128 (by decide)
  have h6 : Entails.eval a c148 := h 147 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨53, by decide⟩, false), (⟨56, by decide⟩, false), (⟨52, by decide⟩, false), (⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c678, some c188, some c145, some c302, some c303, some c148, some c213, some c192, some c250, some c124, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c678, c188, c145, c302, c303, c148, c213, c192, c250, c124] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c678 := derived678 a h
  have h1 : Entails.eval a c188 := h 187 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c303 := h 302 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c250 := h 249 (by decide)
  have h9 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨19, by decide⟩, true), (⟨51, by decide⟩, false), (⟨50, by decide⟩, false), (⟨24, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c301, some c303, some c211, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c301, c303, c211] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c301 := h 300 (by decide)
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨19, by decide⟩, true), (⟨50, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨31, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c680, some c145, some c188, some c185, some c127, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c680, c145, c188, c185, c127] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c680 := derived680 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨28, by decide⟩, true), (⟨52, by decide⟩, true), (⟨32, by decide⟩, true), (⟨47, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c356, some c368, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c293, c356, c368] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨45, by decide⟩, true), (⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨53, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c145, some c303, some c139, some c239, some c679, some c211, some c315, some c148, some c682, some c369, some c172, some c203, some c3, some c45, some c87, some c13, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c145, c303, c139, c239, c679, c211, c315, c148, c682, c369, c172, c203, c3, c45, c87, c13] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c239 := h 238 (by decide)
  have h4 : Entails.eval a c679 := derived679 a h
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c682 := derived682 a h
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c172 := h 171 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, true), (⟨22, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c126, some c198, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c122, c126, c198] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c126 := h 125 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨23, by decide⟩, false), (⟨53, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c381, some c196, some c188, some c564, some c376, some c145, some c139, some c303, some c433, some c683, some c359, some c355, some c231, some c368, some c291, some c315, some c148, some c213, some c293, some c370, some c241, some c172, some c203, some c684, some c264, some c2, some c45, some c98, some c94, some c78, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c381, c196, c188, c564, c376, c145, c139, c303, c433, c683, c359, c355, c231, c368, c291, c315, c148, c213, c293, c370, c241, c172, c203, c684, c264, c2, c45, c98, c94, c78] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c381 := h 380 (by decide)
  have h1 : Entails.eval a c196 := h 195 (by decide)
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c564 := derived564 a h
  have h4 : Entails.eval a c376 := h 375 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c433 := derived433 a h
  have h9 : Entails.eval a c683 := derived683 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c231 := h 230 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c291 := h 290 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c213 := h 212 (by decide)
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c370 := h 369 (by decide)
  have h20 : Entails.eval a c241 := h 240 (by decide)
  have h21 : Entails.eval a c172 := h 171 (by decide)
  have h22 : Entails.eval a c203 := h 202 (by decide)
  have h23 : Entails.eval a c684 := derived684 a h
  have h24 : Entails.eval a c264 := h 263 (by decide)
  have h25 : Entails.eval a c2 := h 1 (by decide)
  have h26 : Entails.eval a c45 := h 44 (by decide)
  have h27 : Entails.eval a c98 := h 97 (by decide)
  have h28 : Entails.eval a c94 := h 93 (by decide)
  have h29 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨53, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c311, some c309, some c215, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c311, c309, c215] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c311 := h 310 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨16, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c686, some c119, some c685, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c196, c686, c119, c685] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c686 := derived686 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c685 := derived685 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨32, by decide⟩, true), (⟨47, by decide⟩, false), (⟨26, by decide⟩, false), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c255, some c239, some c359, some c355, some c368, some c291, some c315, some c213, some c264, some c2, some c45, some c98, some c94, some c78, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c255, c239, c359, c355, c368, c291, c315, c213, c264, c2, c45, c98, c94, c78] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c315 := h 314 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c264 := h 263 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c94 := h 93 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨20, by decide⟩, false), (⟨12, by decide⟩, false), (⟨46, by decide⟩, false), (⟨45, by decide⟩, true), (⟨19, by decide⟩, true), (⟨47, by decide⟩, false), (⟨10, by decide⟩, true), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c370, some c241, some c172, some c203, some c684, some c126, some c231, some c198, some c169, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c370, c241, c172, c203, c684, c126, c231, c198, c169] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c370 := h 369 (by decide)
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c684 := derived684 a h
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c231 := h 230 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c631, some c188, some c196, some c564, some c376, some c145, some c139, some c303, some c688, some c681, some c211, some c433, some c315, some c363, some c148, some c213, some c689, some c293, some c682, some c371, some c250, some c172, some c2, some c203, some c45, some c3, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c260, c631, c188, c196, c564, c376, c145, c139, c303, c688, c681, c211, c433, c315, c363, c148, c213, c689, c293, c682, c371, c250, c172, c2, c203, c45, c3] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c564 := derived564 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c688 := derived688 a h
  have h10 : Entails.eval a c681 := derived681 a h
  have h11 : Entails.eval a c211 := h 210 (by decide)
  have h12 : Entails.eval a c433 := derived433 a h
  have h13 : Entails.eval a c315 := h 314 (by decide)
  have h14 : Entails.eval a c363 := h 362 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c213 := h 212 (by decide)
  have h17 : Entails.eval a c689 := derived689 a h
  have h18 : Entails.eval a c293 := h 292 (by decide)
  have h19 : Entails.eval a c682 := derived682 a h
  have h20 : Entails.eval a c371 := h 370 (by decide)
  have h21 : Entails.eval a c250 := h 249 (by decide)
  have h22 : Entails.eval a c172 := h 171 (by decide)
  have h23 : Entails.eval a c2 := h 1 (by decide)
  have h24 : Entails.eval a c203 := h 202 (by decide)
  have h25 : Entails.eval a c45 := h 44 (by decide)
  have h26 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨27, by decide⟩, true), (⟨53, by decide⟩, true), (⟨19, by decide⟩, false), (⟨51, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c688, some c433, some c239, some c134, some c363, some c291, some c371, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c688, c433, c239, c134, c363, c291, c371] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c688 := derived688 a h
  have h1 : Entails.eval a c433 := derived433 a h
  have h2 : Entails.eval a c239 := h 238 (by decide)
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c363 := h 362 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨42, by decide⟩, false), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨51, by decide⟩, true), (⟨32, by decide⟩, true), (⟨10, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c371, some c291, some c233, some c2, some c83, some c81, some c98, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c371, c291, c233, c2, c83, c81, c98] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c371 := h 370 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨31, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c311, some c581, some c631, some c188, some c196, some c564, some c376, some c268, some c687, some c215, some c312, some c319, some c691, some c173, some c692, some c359, some c180, some c369, some c233, some c198, some c176, some c124, some c142, some c203, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c260, c311, c581, c631, c188, c196, c564, c376, c268, c687, c215, c312, c319, c691, c173, c692, c359, c180, c369, c233, c198, c176, c124, c142, c203] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c311 := h 310 (by decide)
  have h2 : Entails.eval a c581 := derived581 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c188 := h 187 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c564 := derived564 a h
  have h7 : Entails.eval a c376 := h 375 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c687 := derived687 a h
  have h10 : Entails.eval a c215 := h 214 (by decide)
  have h11 : Entails.eval a c312 := h 311 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c691 := derived691 a h
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c692 := derived692 a h
  have h16 : Entails.eval a c359 := h 358 (by decide)
  have h17 : Entails.eval a c180 := h 179 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c233 := h 232 (by decide)
  have h20 : Entails.eval a c198 := h 197 (by decide)
  have h21 : Entails.eval a c176 := h 175 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c142 := h 141 (by decide)
  have h24 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c694 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨47, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨51, by decide⟩, true), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f694 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c173, some c211, some c319, some c359, some c180, some c369, some c198, some c176, some c113, some c122, some c1, some c203, some c43, some c144, some c13, some c315, some c45, some c293, some c35, some c84, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p694 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked694 : lratChecker f694 p694 = .success := by decide +kernel
theorem unsat694 : Unsatisfiable (PosFin 57) f694 := by
  apply lratCheckerSound f694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p694
  · intro a ha; simp [p694] at ha; subst a; trivial
  · exact checked694
theorem derived694 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c694 := by
  apply localUnsat_implies_entails f694 [c173, c211, c319, c359, c180, c369, c198, c176, c113, c122, c1, c203, c43, c144, c13, c315, c45, c293, c35, c84] c694 unsat694 (by rfl) a
  have h0 : Entails.eval a c173 := h 172 (by decide)
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c180 := h 179 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c176 := h 175 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c43 := h 42 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c315 := h 314 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c293 := h 292 (by decide)
  have h18 : Entails.eval a c35 := h 34 (by decide)
  have h19 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c695 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨51, by decide⟩, true), (⟨32, by decide⟩, true), (⟨31, by decide⟩, false), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨54, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f695 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c211, some c319, some c173, some c694, some c370, some c371, some c176, some c293, some c315, some c114, some c144, some c235, some c203, some c684, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p695 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked695 : lratChecker f695 p695 = .success := by decide +kernel
theorem unsat695 : Unsatisfiable (PosFin 57) f695 := by
  apply lratCheckerSound f695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p695
  · intro a ha; simp [p695] at ha; subst a; trivial
  · exact checked695
theorem derived695 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c695 := by
  apply localUnsat_implies_entails f695 [c211, c319, c173, c694, c370, c371, c176, c293, c315, c114, c144, c235, c203, c684] c695 unsat695 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c694 := derived694 a h
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c176 := h 175 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c315 := h 314 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c235 := h 234 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c684 := derived684 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c696 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨20, by decide⟩, false), (⟨26, by decide⟩, false), (⟨41, by decide⟩, true), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨10, by decide⟩, true), (⟨50, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f696 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c315, some c356, some c136, some c250, some c203, some c2, some c3, some c45, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p696 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked696 : lratChecker f696 p696 = .success := by decide +kernel
theorem unsat696 : Unsatisfiable (PosFin 57) f696 := by
  apply lratCheckerSound f696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p696
  · intro a ha; simp [p696] at ha; subst a; trivial
  · exact checked696
theorem derived696 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c696 := by
  apply localUnsat_implies_entails f696 [c315, c356, c136, c250, c203, c2, c3, c45] c696 unsat696 (by rfl) a
  have h0 : Entails.eval a c315 := h 314 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c136 := h 135 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c697 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f697 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c631, some c188, some c196, some c564, some c376, some c311, some c581, some c693, some c211, some c319, some c215, some c258, some c261, some c695, some c433, some c578, some c363, some c295, some c368, some c371, some c169, some c288, some c198, some c315, some c213, some c696, some c689, some c241, some c6, some c91, some c89, some c620, some c16, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p697 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]]
theorem checked697 : lratChecker f697 p697 = .success := by decide +kernel
theorem unsat697 : Unsatisfiable (PosFin 57) f697 := by
  apply lratCheckerSound f697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p697
  · intro a ha; simp [p697] at ha; subst a; trivial
  · exact checked697
theorem derived697 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c697 := by
  apply localUnsat_implies_entails f697 [c260, c631, c188, c196, c564, c376, c311, c581, c693, c211, c319, c215, c258, c261, c695, c433, c578, c363, c295, c368, c371, c169, c288, c198, c315, c213, c696, c689, c241, c6, c91, c89, c620, c16] c697 unsat697 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c188 := h 187 (by decide)
  have h3 : Entails.eval a c196 := h 195 (by decide)
  have h4 : Entails.eval a c564 := derived564 a h
  have h5 : Entails.eval a c376 := h 375 (by decide)
  have h6 : Entails.eval a c311 := h 310 (by decide)
  have h7 : Entails.eval a c581 := derived581 a h
  have h8 : Entails.eval a c693 := derived693 a h
  have h9 : Entails.eval a c211 := h 210 (by decide)
  have h10 : Entails.eval a c319 := h 318 (by decide)
  have h11 : Entails.eval a c215 := h 214 (by decide)
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c261 := h 260 (by decide)
  have h14 : Entails.eval a c695 := derived695 a h
  have h15 : Entails.eval a c433 := derived433 a h
  have h16 : Entails.eval a c578 := derived578 a h
  have h17 : Entails.eval a c363 := h 362 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  have h19 : Entails.eval a c368 := h 367 (by decide)
  have h20 : Entails.eval a c371 := h 370 (by decide)
  have h21 : Entails.eval a c169 := h 168 (by decide)
  have h22 : Entails.eval a c288 := h 287 (by decide)
  have h23 : Entails.eval a c198 := h 197 (by decide)
  have h24 : Entails.eval a c315 := h 314 (by decide)
  have h25 : Entails.eval a c213 := h 212 (by decide)
  have h26 : Entails.eval a c696 := derived696 a h
  have h27 : Entails.eval a c689 := derived689 a h
  have h28 : Entails.eval a c241 := h 240 (by decide)
  have h29 : Entails.eval a c6 := h 5 (by decide)
  have h30 : Entails.eval a c91 := h 90 (by decide)
  have h31 : Entails.eval a c89 := h 88 (by decide)
  have h32 : Entails.eval a c620 := derived620 a h
  have h33 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c698 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨55, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f698 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c631, some c697, some c690, some c258, some c687, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p698 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked698 : lratChecker f698 p698 = .success := by decide +kernel
theorem unsat698 : Unsatisfiable (PosFin 57) f698 := by
  apply lratCheckerSound f698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p698
  · intro a ha; simp [p698] at ha; subst a; trivial
  · exact checked698
theorem derived698 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c698 := by
  apply localUnsat_implies_entails f698 [c260, c631, c697, c690, c258, c687] c698 unsat698 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c697 := derived697 a h
  have h3 : Entails.eval a c690 := derived690 a h
  have h4 : Entails.eval a c258 := h 257 (by decide)
  have h5 : Entails.eval a c687 := derived687 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c699 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨28, by decide⟩, true), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f699 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c203, some c148, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p699 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked699 : lratChecker f699 p699 = .success := by decide +kernel
theorem unsat699 : Unsatisfiable (PosFin 57) f699 := by
  apply lratCheckerSound f699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p699
  · intro a ha; simp [p699] at ha; subst a; trivial
  · exact checked699
theorem derived699 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c699 := by
  apply localUnsat_implies_entails f699 [c204, c203, c148] c699 unsat699 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c700 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨48, by decide⟩, false), (⟨47, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f700 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c244, some c125, some c132, some c266, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p700 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked700 : lratChecker f700 p700 = .success := by decide +kernel
theorem unsat700 : Unsatisfiable (PosFin 57) f700 := by
  apply lratCheckerSound f700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p700
  · intro a ha; simp [p700] at ha; subst a; trivial
  · exact checked700
theorem derived700 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c700 := by
  apply localUnsat_implies_entails f700 [c244, c125, c132, c266] c700 unsat700 (by rfl) a
  have h0 : Entails.eval a c244 := h 243 (by decide)
  have h1 : Entails.eval a c125 := h 124 (by decide)
  have h2 : Entails.eval a c132 := h 131 (by decide)
  have h3 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c701 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨24, by decide⟩, true), (⟨48, by decide⟩, false), (⟨19, by decide⟩, true), (⟨47, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f701 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c92, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p701 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked701 : lratChecker f701 p701 = .success := by decide +kernel
theorem unsat701 : Unsatisfiable (PosFin 57) f701 := by
  apply lratCheckerSound f701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p701
  · intro a ha; simp [p701] at ha; subst a; trivial
  · exact checked701
theorem derived701 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c701 := by
  apply localUnsat_implies_entails f701 [c620, c92] c701 unsat701 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c702 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f702 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c20, some c13, some c109, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p702 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked702 : lratChecker f702 p702 = .success := by decide +kernel
theorem unsat702 : Unsatisfiable (PosFin 57) f702 := by
  apply lratCheckerSound f702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p702
  · intro a ha; simp [p702] at ha; subst a; trivial
  · exact checked702
theorem derived702 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c702 := by
  apply localUnsat_implies_entails f702 [c16, c20, c13, c109] c702 unsat702 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c703 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨31, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f703 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c39, some c54, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p703 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked703 : lratChecker f703 p703 = .success := by decide +kernel
theorem unsat703 : Unsatisfiable (PosFin 57) f703 := by
  apply lratCheckerSound f703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p703
  · intro a ha; simp [p703] at ha; subst a; trivial
  · exact checked703
theorem derived703 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c703 := by
  apply localUnsat_implies_entails f703 [c215, c39, c54] c703 unsat703 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c704 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, true), (⟨7, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f704 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c620, some c703, some c268, some c267, some c128, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p704 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked704 : lratChecker f704 p704 = .success := by decide +kernel
theorem unsat704 : Unsatisfiable (PosFin 57) f704 := by
  apply lratCheckerSound f704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p704
  · intro a ha; simp [p704] at ha; subst a; trivial
  · exact checked704
theorem derived704 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c704 := by
  apply localUnsat_implies_entails f704 [c620, c703, c268, c267, c128] c704 unsat704 (by rfl) a
  have h0 : Entails.eval a c620 := derived620 a h
  have h1 : Entails.eval a c703 := derived703 a h
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c705 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f705 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c699, some c145, some c152, some c316, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p705 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked705 : lratChecker f705 p705 = .success := by decide +kernel
theorem unsat705 : Unsatisfiable (PosFin 57) f705 := by
  apply lratCheckerSound f705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p705
  · intro a ha; simp [p705] at ha; subst a; trivial
  · exact checked705
theorem derived705 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c705 := by
  apply localUnsat_implies_entails f705 [c204, c699, c145, c152, c316] c705 unsat705 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c699 := derived699 a h
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c706 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f706 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c125, some c128, some c264, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p706 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked706 : lratChecker f706 p706 = .success := by decide +kernel
theorem unsat706 : Unsatisfiable (PosFin 57) f706 := by
  apply lratCheckerSound f706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p706
  · intro a ha; simp [p706] at ha; subst a; trivial
  · exact checked706
theorem derived706 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c706 := by
  apply localUnsat_implies_entails f706 [c125, c128, c264] c706 unsat706 (by rfl) a
  have h0 : Entails.eval a c125 := h 124 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c707 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f707 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c239, some c291, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p707 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked707 : lratChecker f707 p707 = .success := by decide +kernel
theorem unsat707 : Unsatisfiable (PosFin 57) f707 := by
  apply lratCheckerSound f707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p707
  · intro a ha; simp [p707] at ha; subst a; trivial
  · exact checked707
theorem derived707 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c707 := by
  apply localUnsat_implies_entails f707 [c92, c239, c291] c707 unsat707 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c239 := h 238 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c708 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨9, by decide⟩, true), (⟨43, by decide⟩, true), (⟨46, by decide⟩, true), (⟨31, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f708 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c312, some c290, some c141, some c143, some c316, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p708 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked708 : lratChecker f708 p708 = .success := by decide +kernel
theorem unsat708 : Unsatisfiable (PosFin 57) f708 := by
  apply lratCheckerSound f708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p708
  · intro a ha; simp [p708] at ha; subst a; trivial
  · exact checked708
theorem derived708 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c708 := by
  apply localUnsat_implies_entails f708 [c319, c312, c290, c141, c143, c316] c708 unsat708 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c312 := h 311 (by decide)
  have h2 : Entails.eval a c290 := h 289 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c709 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f709 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c706, some c268, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p709 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked709 : lratChecker f709 p709 = .success := by decide +kernel
theorem unsat709 : Unsatisfiable (PosFin 57) f709 := by
  apply lratCheckerSound f709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p709
  · intro a ha; simp [p709] at ha; subst a; trivial
  · exact checked709
theorem derived709 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c709 := by
  apply localUnsat_implies_entails f709 [c706, c268] c709 unsat709 (by rfl) a
  have h0 : Entails.eval a c706 := derived706 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c710 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨44, by decide⟩, false), (⟨42, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f710 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c121, some c123, some c234, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p710 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked710 : lratChecker f710 p710 = .success := by decide +kernel
theorem unsat710 : Unsatisfiable (PosFin 57) f710 := by
  apply lratCheckerSound f710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p710
  · intro a ha; simp [p710] at ha; subst a; trivial
  · exact checked710
theorem derived710 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c710 := by
  apply localUnsat_implies_entails f710 [c121, c123, c234] c710 unsat710 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c711 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨12, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f711 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c139, some c173, some c176, some c370, some c369, some c180, some c198, some c708, some c215, some c710, some c261, some c125, some c128, some c234, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p711 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked711 : lratChecker f711 p711 = .success := by decide +kernel
theorem unsat711 : Unsatisfiable (PosFin 57) f711 := by
  apply lratCheckerSound f711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p711
  · intro a ha; simp [p711] at ha; subst a; trivial
  · exact checked711
theorem derived711 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c711 := by
  apply localUnsat_implies_entails f711 [c120, c139, c173, c176, c370, c369, c180, c198, c708, c215, c710, c261, c125, c128, c234] c711 unsat711 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c173 := h 172 (by decide)
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c370 := h 369 (by decide)
  have h5 : Entails.eval a c369 := h 368 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c708 := derived708 a h
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c710 := derived710 a h
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  have h13 : Entails.eval a c128 := h 127 (by decide)
  have h14 : Entails.eval a c234 := h 233 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c712 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨12, by decide⟩, true), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f712 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c709, some c211, some c711, some c120, some c119, some c7, some c125, some c128, some c319, some c701, some c265, some c295, some c132, some c366, some c240, some c198, some c171, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p712 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked712 : lratChecker f712 p712 = .success := by decide +kernel
theorem unsat712 : Unsatisfiable (PosFin 57) f712 := by
  apply lratCheckerSound f712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p712
  · intro a ha; simp [p712] at ha; subst a; trivial
  · exact checked712
theorem derived712 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c712 := by
  apply localUnsat_implies_entails f712 [c709, c211, c711, c120, c119, c7, c125, c128, c319, c701, c265, c295, c132, c366, c240, c198, c171] c712 unsat712 (by rfl) a
  have h0 : Entails.eval a c709 := derived709 a h
  have h1 : Entails.eval a c211 := h 210 (by decide)
  have h2 : Entails.eval a c711 := derived711 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c701 := derived701 a h
  have h10 : Entails.eval a c265 := h 264 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c240 := h 239 (by decide)
  have h15 : Entails.eval a c198 := h 197 (by decide)
  have h16 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c713 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨9, by decide⟩, true), (⟨45, by decide⟩, true), (⟨27, by decide⟩, false), (⟨47, by decide⟩, false), (⟨12, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f713 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c136, some c171, some c318, some c368, some c295, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p713 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked713 : lratChecker f713 p713 = .success := by decide +kernel
theorem unsat713 : Unsatisfiable (PosFin 57) f713 := by
  apply lratCheckerSound f713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p713
  · intro a ha; simp [p713] at ha; subst a; trivial
  · exact checked713
theorem derived713 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c713 := by
  apply localUnsat_implies_entails f713 [c136, c171, c318, c368, c295] c713 unsat713 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c368 := h 367 (by decide)
  have h4 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived713

end CochromaticTwenty.Certificates.B16_0_2Enumerating
