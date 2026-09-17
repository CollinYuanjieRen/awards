import MerLeanExperiment.Certificates.B16_1_2.Steps0100_0199

/-! Generated from the actual pinned b16_1_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_1_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c594 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨50, by decide⟩, false), (⟨27, by decide⟩, true), (⟨51, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨32, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c260, some c548, some c233, some c283, some c346, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c260, c548, c233, c283, c346] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c260 := h 259 (by decide)
  have h1 : Entails.eval a c548 := derived548 a h
  have h2 : Entails.eval a c233 := h 232 (by decide)
  have h3 : Entails.eval a c283 := h 282 (by decide)
  have h4 : Entails.eval a c346 := h 345 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨51, by decide⟩, false), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c36, some c268, some c592, some c388, some c315, some c63, some c124, some c67, some c321, some c593, some c594, some c357, some c352, some c283, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c393, c36, c268, c592, c388, c315, c63, c124, c67, c321, c593, c594, c357, c352, c283] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c592 := derived592 a h
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c321 := h 320 (by decide)
  have h10 : Entails.eval a c593 := derived593 a h
  have h11 : Entails.eval a c594 := derived594 a h
  have h12 : Entails.eval a c357 := h 356 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c309, some c260, some c221, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c309, c260, c221] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c309 := h 308 (by decide)
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c221 := h 220 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c114, some c108, some c121, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c114, c108, c121] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c114 := h 113 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨16, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c597, some c117, some c9, some c105, some c202, some c121, some c14, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c597, c117, c9, c105, c202, c121, c14] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c597 := derived597 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c268, some c8, some c592, some c522, some c388, some c393, some c595, some c215, some c357, some c352, some c283, some c596, some c598, some c65, some c327, some c313, some c436, some c107, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c36, c268, c8, c592, c522, c388, c393, c595, c215, c357, c352, c283, c596, c598, c65, c327, c313, c436, c107] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c592 := derived592 a h
  have h4 : Entails.eval a c522 := derived522 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c393 := h 392 (by decide)
  have h7 : Entails.eval a c595 := derived595 a h
  have h8 : Entails.eval a c215 := h 214 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c352 := h 351 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c596 := derived596 a h
  have h13 : Entails.eval a c598 := derived598 a h
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c327 := h 326 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c436 := derived436 a h
  have h18 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨51, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c436, some c67, some c106, some c124, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c436, c67, c106, c124] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c436 := derived436 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨51, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨49, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c415, some c106, some c128, some c260, some c120, some c45, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c9, c415, c106, c128, c260, c120, c45] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c415 := derived415 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c260 := h 259 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨35, by decide⟩, true), (⟨2, by decide⟩, true), (⟨33, by decide⟩, true), (⟨5, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c221, some c38, some c48, some c293, some c275, some c371, some c230, some c295, some c270, some c228, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c221, c38, c48, c293, c275, c371, c230, c295, c270, c228] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c221 := h 220 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c275 := h 274 (by decide)
  have h5 : Entails.eval a c371 := h 370 (by decide)
  have h6 : Entails.eval a c230 := h 229 (by decide)
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨4, by decide⟩, false), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨51, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, false), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c268, some c215, some c388, some c601, some c71, some c117, some c522, some c120, some c79, some c602, some c260, some c132, some c10, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c592, c268, c215, c388, c601, c71, c117, c522, c120, c79, c602, c260, c132, c10] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c601 := derived601 a h
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c522 := derived522 a h
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c602 := derived602 a h
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c592, some c599, some c600, some c36, some c268, some c8, some c522, some c327, some c224, some c65, some c601, some c117, some c603, some c87, some c110, some c298, some c121, some c103, some c96, some c180, some c293, some c2, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c388, c592, c599, c600, c36, c268, c8, c522, c327, c224, c65, c601, c117, c603, c87, c110, c298, c121, c103, c96, c180, c293, c2] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c599 := derived599 a h
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c522 := derived522 a h
  have h8 : Entails.eval a c327 := h 326 (by decide)
  have h9 : Entails.eval a c224 := h 223 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c601 := derived601 a h
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c603 := derived603 a h
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c298 := h 297 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c96 := h 95 (by decide)
  have h20 : Entails.eval a c180 := h 179 (by decide)
  have h21 : Entails.eval a c293 := h 292 (by decide)
  have h22 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c268, some c592, some c215, some c357, some c604, some c63, some c283, some c79, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c36, c268, c592, c215, c357, c604, c63, c283, c79] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c592 := derived592 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c604 := derived604 a h
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, false), (⟨32, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c65, some c77, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c285, c65, c77] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨51, by decide⟩, true), (⟨16, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c194, some c190, some c202, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c194, c190, c202] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c190 := h 189 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c522, some c388, some c36, some c8, some c268, some c599, some c600, some c605, some c318, some c321, some c328, some c63, some c124, some c13, some c89, some c114, some c407, some c607, some c182, some c367, some c464, some c9, some c141, some c70, some c71, some c240, some c172, some c139, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c592, c522, c388, c36, c8, c268, c599, c600, c605, c318, c321, c328, c63, c124, c13, c89, c114, c407, c607, c182, c367, c464, c9, c141, c70, c71, c240, c172, c139] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c599 := derived599 a h
  have h7 : Entails.eval a c600 := derived600 a h
  have h8 : Entails.eval a c605 := derived605 a h
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c13 := h 12 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c407 := derived407 a h
  have h18 : Entails.eval a c607 := derived607 a h
  have h19 : Entails.eval a c182 := h 181 (by decide)
  have h20 : Entails.eval a c367 := h 366 (by decide)
  have h21 : Entails.eval a c464 := derived464 a h
  have h22 : Entails.eval a c9 := h 8 (by decide)
  have h23 : Entails.eval a c141 := h 140 (by decide)
  have h24 : Entails.eval a c70 := h 69 (by decide)
  have h25 : Entails.eval a c71 := h 70 (by decide)
  have h26 : Entails.eval a c240 := h 239 (by decide)
  have h27 : Entails.eval a c172 := h 171 (by decide)
  have h28 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨51, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c33, some c41, some c182, some c367, some c173, some c289, some c9, some c141, some c71, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c33, c41, c182, c367, c173, c289, c9, c141, c71] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c367 := h 366 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c289 := h 288 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c407, some c147, some c357, some c522, some c607, some c207, some c156, some c592, some c124, some c79, some c609, some c134, some c211, some c235, some c324, some c268, some c221, some c153, some c132, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c388, c407, c147, c357, c522, c607, c207, c156, c592, c124, c79, c609, c134, c211, c235, c324, c268, c221, c153, c132] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c522 := derived522 a h
  have h5 : Entails.eval a c607 := derived607 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c592 := derived592 a h
  have h9 : Entails.eval a c124 := h 123 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c609 := derived609 a h
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c211 := h 210 (by decide)
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c324 := h 323 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c153 := h 152 (by decide)
  have h19 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c522, some c607, some c608, some c320, some c592, some c407, some c207, some c147, some c156, some c610, some c106, some c87, some c117, some c182, some c609, some c89, some c134, some c266, some c31, some c51, some c324, some c221, some c153, some c132, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c388, c522, c607, c608, c320, c592, c407, c207, c147, c156, c610, c106, c87, c117, c182, c609, c89, c134, c266, c31, c51, c324, c221, c153, c132] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c607 := derived607 a h
  have h3 : Entails.eval a c608 := derived608 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c592 := derived592 a h
  have h6 : Entails.eval a c407 := derived407 a h
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c156 := h 155 (by decide)
  have h10 : Entails.eval a c610 := derived610 a h
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c182 := h 181 (by decide)
  have h15 : Entails.eval a c609 := derived609 a h
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c134 := h 133 (by decide)
  have h18 : Entails.eval a c266 := h 265 (by decide)
  have h19 : Entails.eval a c31 := h 30 (by decide)
  have h20 : Entails.eval a c51 := h 50 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c221 := h 220 (by decide)
  have h23 : Entails.eval a c153 := h 152 (by decide)
  have h24 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c224, some c156, some c264, some c181, some c204, some c88, some c20, some c121, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c13, c224, c156, c264, c181, c204, c88, c20, c121] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c224 := h 223 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c204 := h 203 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨20, by decide⟩, true), (⟨52, by decide⟩, true), (⟨43, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c40, some c12, some c181, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c40, c12, c181] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c40 := h 39 (by decide)
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c13, some c266, some c612, some c327, some c316, some c31, some c275, some c613, some c121, some c20, some c129, some c177, some c38, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c5, c13, c266, c612, c327, c316, c31, c275, c613, c121, c20, c129, c177, c38] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c612 := derived612 a h
  have h4 : Entails.eval a c327 := h 326 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c613 := derived613 a h
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c20 := h 19 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  have h12 : Entails.eval a c177 := h 176 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c13, some c608, some c320, some c614, some c55, some c41, some c268, some c298, some c384, some c385, some c31, some c248, some c272, some c133, some c48, some c156, some c121, some c316, some c12, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c5, c13, c608, c320, c614, c55, c41, c268, c298, c384, c385, c31, c248, c272, c133, c48, c156, c121, c316, c12] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c608 := derived608 a h
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c614 := derived614 a h
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c384 := h 383 (by decide)
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c156 := h 155 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c316 := h 315 (by decide)
  have h19 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨47, by decide⟩, true), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c322, some c320, some c388, some c55, some c41, some c268, some c298, some c384, some c289, some c228, some c31, some c248, some c368, some c274, some c133, some c316, some c48, some c4, some c121, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c608, c322, c320, c388, c55, c41, c268, c298, c384, c289, c228, c31, c248, c368, c274, c133, c316, c48, c4, c121] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c322 := h 321 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c268 := h 267 (by decide)
  have h7 : Entails.eval a c298 := h 297 (by decide)
  have h8 : Entails.eval a c384 := h 383 (by decide)
  have h9 : Entails.eval a c289 := h 288 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c248 := h 247 (by decide)
  have h13 : Entails.eval a c368 := h 367 (by decide)
  have h14 : Entails.eval a c274 := h 273 (by decide)
  have h15 : Entails.eval a c133 := h 132 (by decide)
  have h16 : Entails.eval a c316 := h 315 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c4 := h 3 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨47, by decide⟩, true), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c275, some c273, some c31, some c221, some c245, some c293, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c275, c273, c31, c221, c245, c293] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c275 := h 274 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c221 := h 220 (by decide)
  have h4 : Entails.eval a c245 := h 244 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨29, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c183, some c608, some c320, some c388, some c322, some c616, some c567, some c228, some c617, some c224, some c248, some c316, some c181, some c191, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c183, c608, c320, c388, c322, c616, c567, c228, c617, c224, c248, c316, c181, c191] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c183 := h 182 (by decide)
  have h1 : Entails.eval a c608 := derived608 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c322 := h 321 (by decide)
  have h5 : Entails.eval a c616 := derived616 a h
  have h6 : Entails.eval a c567 := derived567 a h
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c617 := derived617 a h
  have h9 : Entails.eval a c224 := h 223 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c181 := h 180 (by decide)
  have h13 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c611, some c388, some c522, some c607, some c608, some c320, some c592, some c106, some c87, some c110, some c117, some c13, some c5, some c615, some c203, some c618, some c141, some c71, some c215, some c268, some c580, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c611, c388, c522, c607, c608, c320, c592, c106, c87, c110, c117, c13, c5, c615, c203, c618, c141, c71, c215, c268, c580] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c611 := derived611 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c607 := derived607 a h
  have h4 : Entails.eval a c608 := derived608 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c615 := derived615 a h
  have h14 : Entails.eval a c203 := h 202 (by decide)
  have h15 : Entails.eval a c618 := derived618 a h
  have h16 : Entails.eval a c141 := h 140 (by decide)
  have h17 : Entails.eval a c71 := h 70 (by decide)
  have h18 : Entails.eval a c215 := h 214 (by decide)
  have h19 : Entails.eval a c268 := h 267 (by decide)
  have h20 : Entails.eval a c580 := derived580 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c266, some c55, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c268, c266, c55] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨30, by decide⟩, true), (⟨6, by decide⟩, false), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨31, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c235, some c275, some c224, some c237, some c53, some c327, some c81, some c282, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c55, c235, c275, c224, c237, c53, c327, c81, c282] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c235 := h 234 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c237 := h 236 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c320, some c215, some c357, some c592, some c388, some c183, some c203, some c9, some c71, some c141, some c322, some c228, some c621, some c274, some c139, some c270, some c221, some c245, some c146, some c229, some c312, some c177, some c75, some c10, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c608, c320, c215, c357, c592, c388, c183, c203, c9, c71, c141, c322, c228, c621, c274, c139, c270, c221, c245, c146, c229, c312, c177, c75, c10] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c592 := derived592 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  have h11 : Entails.eval a c322 := h 321 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c621 := derived621 a h
  have h14 : Entails.eval a c274 := h 273 (by decide)
  have h15 : Entails.eval a c139 := h 138 (by decide)
  have h16 : Entails.eval a c270 := h 269 (by decide)
  have h17 : Entails.eval a c221 := h 220 (by decide)
  have h18 : Entails.eval a c245 := h 244 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c229 := h 228 (by decide)
  have h21 : Entails.eval a c312 := h 311 (by decide)
  have h22 : Entails.eval a c177 := h 176 (by decide)
  have h23 : Entails.eval a c75 := h 74 (by decide)
  have h24 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c160, some c228, some c139, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c160, c228, c139] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c160 := h 159 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨15, by decide⟩, true), (⟨23, by decide⟩, true), (⟨16, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c623, some c326, some c221, some c153, some c132, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c623, c326, c221, c153, c132] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c623 := derived623 a h
  have h1 : Entails.eval a c326 := h 325 (by decide)
  have h2 : Entails.eval a c221 := h 220 (by decide)
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨43, by decide⟩, false), (⟨35, by decide⟩, true), (⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c320, some c215, some c357, some c622, some c624, some c235, some c621, some c326, some c221, some c153, some c129, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c608, c320, c215, c357, c622, c624, c235, c621, c326, c221, c153, c129] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c215 := h 214 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c622 := derived622 a h
  have h5 : Entails.eval a c624 := derived624 a h
  have h6 : Entails.eval a c235 := h 234 (by decide)
  have h7 : Entails.eval a c621 := derived621 a h
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨43, by decide⟩, false), (⟨3, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c608, some c320, some c124, some c13, some c620, some c215, some c79, some c5, some c522, some c625, some c14, some c90, some c206, some c187, some c20, some c103, some c120, some c384, some c101, some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c592, c608, c320, c124, c13, c620, c215, c79, c5, c522, c625, c14, c90, c206, c187, c20, c103, c120, c384, c101] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c608 := derived608 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c620 := derived620 a h
  have h6 : Entails.eval a c215 := h 214 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c522 := derived522 a h
  have h10 : Entails.eval a c625 := derived625 a h
  have h11 : Entails.eval a c14 := h 13 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c187 := h 186 (by decide)
  have h15 : Entails.eval a c20 := h 19 (by decide)
  have h16 : Entails.eval a c103 := h 102 (by decide)
  have h17 : Entails.eval a c120 := h 119 (by decide)
  have h18 : Entails.eval a c384 := h 383 (by decide)
  have h19 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c627 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c320, some c592, some c522, some c388, some c607, some c611, some c619, some c124, some c13, some c5, some c620, some c215, some c626, some c367, some c371, some c379, some c44, some c103, some c624, some c289, some c203, some c141, some c9, some c71, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked627 : lratChecker f627 p627 = .success := by decide +kernel
theorem unsat627 : Unsatisfiable (PosFin 57) f627 := by
  apply lratCheckerSound f627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p627
  · intro a ha; simp [p627] at ha; subst a; trivial
  · exact checked627
theorem derived627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c627 := by
  apply localUnsat_implies_entails f627 [c608, c320, c592, c522, c388, c607, c611, c619, c124, c13, c5, c620, c215, c626, c367, c371, c379, c44, c103, c624, c289, c203, c141, c9, c71] c627 unsat627 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c592 := derived592 a h
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c607 := derived607 a h
  have h6 : Entails.eval a c611 := derived611 a h
  have h7 : Entails.eval a c619 := derived619 a h
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c620 := derived620 a h
  have h12 : Entails.eval a c215 := h 214 (by decide)
  have h13 : Entails.eval a c626 := derived626 a h
  have h14 : Entails.eval a c367 := h 366 (by decide)
  have h15 : Entails.eval a c371 := h 370 (by decide)
  have h16 : Entails.eval a c379 := h 378 (by decide)
  have h17 : Entails.eval a c44 := h 43 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c624 := derived624 a h
  have h20 : Entails.eval a c289 := h 288 (by decide)
  have h21 : Entails.eval a c203 := h 202 (by decide)
  have h22 : Entails.eval a c141 := h 140 (by decide)
  have h23 : Entails.eval a c9 := h 8 (by decide)
  have h24 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c628 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c407, some c147, some c207, some c609, some c156, some c134, some c327, some c31, some c211, some c79, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked628 : lratChecker f628 p628 = .success := by decide +kernel
theorem unsat628 : Unsatisfiable (PosFin 57) f628 := by
  apply lratCheckerSound f628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p628
  · intro a ha; simp [p628] at ha; subst a; trivial
  · exact checked628
theorem derived628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c628 := by
  apply localUnsat_implies_entails f628 [c407, c147, c207, c609, c156, c134, c327, c31, c211, c79] c628 unsat628 (by rfl) a
  have h0 : Entails.eval a c407 := derived407 a h
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c609 := derived609 a h
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c629 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c167, some c79, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked629 : lratChecker f629 p629 = .success := by decide +kernel
theorem unsat629 : Unsatisfiable (PosFin 57) f629 := by
  apply lratCheckerSound f629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p629
  · intro a ha; simp [p629] at ha; subst a; trivial
  · exact checked629
theorem derived629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c629 := by
  apply localUnsat_implies_entails f629 [c23, c167, c79] c629 unsat629 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c167 := h 166 (by decide)
  have h2 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c630 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨28, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, true), (⟨39, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c120, some c211, some c60, some c324, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked630 : lratChecker f630 p630 = .success := by decide +kernel
theorem unsat630 : Unsatisfiable (PosFin 57) f630 := by
  apply lratCheckerSound f630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p630
  · intro a ha; simp [p630] at ha; subst a; trivial
  · exact checked630
theorem derived630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c630 := by
  apply localUnsat_implies_entails f630 [c79, c120, c211, c60, c324] c630 unsat630 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c631 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c627, some c608, some c320, some c592, some c522, some c388, some c27, some c407, some c147, some c357, some c629, some c207, some c609, some c628, some c25, some c156, some c134, some c630, some c110, some c31, some c121, some c324, some c60, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked631 : lratChecker f631 p631 = .success := by decide +kernel
theorem unsat631 : Unsatisfiable (PosFin 57) f631 := by
  apply lratCheckerSound f631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p631
  · intro a ha; simp [p631] at ha; subst a; trivial
  · exact checked631
theorem derived631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c631 := by
  apply localUnsat_implies_entails f631 [c627, c608, c320, c592, c522, c388, c27, c407, c147, c357, c629, c207, c609, c628, c25, c156, c134, c630, c110, c31, c121, c324, c60] c631 unsat631 (by rfl) a
  have h0 : Entails.eval a c627 := derived627 a h
  have h1 : Entails.eval a c608 := derived608 a h
  have h2 : Entails.eval a c320 := h 319 (by decide)
  have h3 : Entails.eval a c592 := derived592 a h
  have h4 : Entails.eval a c522 := derived522 a h
  have h5 : Entails.eval a c388 := h 387 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c407 := derived407 a h
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c629 := derived629 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c609 := derived609 a h
  have h13 : Entails.eval a c628 := derived628 a h
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c156 := h 155 (by decide)
  have h16 : Entails.eval a c134 := h 133 (by decide)
  have h17 : Entails.eval a c630 := derived630 a h
  have h18 : Entails.eval a c110 := h 109 (by decide)
  have h19 : Entails.eval a c31 := h 30 (by decide)
  have h20 : Entails.eval a c121 := h 120 (by decide)
  have h21 : Entails.eval a c324 := h 323 (by decide)
  have h22 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c632 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c388, some c631, some c117, some c124, some c106, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked632 : lratChecker f632 p632 = .success := by decide +kernel
theorem unsat632 : Unsatisfiable (PosFin 57) f632 := by
  apply lratCheckerSound f632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p632
  · intro a ha; simp [p632] at ha; subst a; trivial
  · exact checked632
theorem derived632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c632 := by
  apply localUnsat_implies_entails f632 [c592, c388, c631, c117, c124, c106] c632 unsat632 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c633 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true), (⟨9, by decide⟩, false), (⟨5, by decide⟩, false), (⟨31, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c117, some c201, some c147, some c82, some c213, some c134, some c125, some c46, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked633 : lratChecker f633 p633 = .success := by decide +kernel
theorem unsat633 : Unsatisfiable (PosFin 57) f633 := by
  apply lratCheckerSound f633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p633
  · intro a ha; simp [p633] at ha; subst a; trivial
  · exact checked633
theorem derived633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c633 := by
  apply localUnsat_implies_entails f633 [c124, c117, c201, c147, c82, c213, c134, c125, c46] c633 unsat633 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c125 := h 124 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c634 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c320, some c388, some c215, some c147, some c268, some c562, some c44, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked634 : lratChecker f634 p634 = .success := by decide +kernel
theorem unsat634 : Unsatisfiable (PosFin 57) f634 := by
  apply lratCheckerSound f634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p634
  · intro a ha; simp [p634] at ha; subst a; trivial
  · exact checked634
theorem derived634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c634 := by
  apply localUnsat_implies_entails f634 [c608, c320, c388, c215, c147, c268, c562, c44] c634 unsat634 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c562 := derived562 a h
  have h7 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c635 : DefaultClause 57 := directClause [(⟨45, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c592, some c117, some c85, some c9, some c124, some c632, some c393, some c608, some c320, some c522, some c375, some c379, some c174, some c44, some c99, some c160, some c268, some c326, some c624, some c221, some c153, some c23, some c260, some c177, some c369, some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked635 : lratChecker f635 p635 = .success := by decide +kernel
theorem unsat635 : Unsatisfiable (PosFin 57) f635 := by
  apply lratCheckerSound f635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p635
  · intro a ha; simp [p635] at ha; subst a; trivial
  · exact checked635
theorem derived635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c635 := by
  apply localUnsat_implies_entails f635 [c388, c592, c117, c85, c9, c124, c632, c393, c608, c320, c522, c375, c379, c174, c44, c99, c160, c268, c326, c624, c221, c153, c23, c260, c177, c369] c635 unsat635 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c632 := derived632 a h
  have h7 : Entails.eval a c393 := h 392 (by decide)
  have h8 : Entails.eval a c608 := derived608 a h
  have h9 : Entails.eval a c320 := h 319 (by decide)
  have h10 : Entails.eval a c522 := derived522 a h
  have h11 : Entails.eval a c375 := h 374 (by decide)
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c174 := h 173 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c99 := h 98 (by decide)
  have h16 : Entails.eval a c160 := h 159 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c326 := h 325 (by decide)
  have h19 : Entails.eval a c624 := derived624 a h
  have h20 : Entails.eval a c221 := h 220 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c260 := h 259 (by decide)
  have h24 : Entails.eval a c177 := h 176 (by decide)
  have h25 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c636 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c198, some c171, some c202, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false))]
def p636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked636 : lratChecker f636 p636 = .success := by decide +kernel
theorem unsat636 : Unsatisfiable (PosFin 57) f636 := by
  apply lratCheckerSound f636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p636
  · intro a ha; simp [p636] at ha; subst a; trivial
  · exact checked636
theorem derived636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c636 := by
  apply localUnsat_implies_entails f636 [c198, c171, c202] c636 unsat636 (by rfl) a
  have h0 : Entails.eval a c198 := h 197 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c637 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c632, some c393, some c592, some c522, some c388, some c117, some c9, some c85, some c634, some c357, some c82, some c636, some c201, some c173, some c635, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked637 : lratChecker f637 p637 = .success := by decide +kernel
theorem unsat637 : Unsatisfiable (PosFin 57) f637 := by
  apply lratCheckerSound f637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p637
  · intro a ha; simp [p637] at ha; subst a; trivial
  · exact checked637
theorem derived637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c637 := by
  apply localUnsat_implies_entails f637 [c632, c393, c592, c522, c388, c117, c9, c85, c634, c357, c82, c636, c201, c173, c635] c637 unsat637 (by rfl) a
  have h0 : Entails.eval a c632 := derived632 a h
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c592 := derived592 a h
  have h3 : Entails.eval a c522 := derived522 a h
  have h4 : Entails.eval a c388 := h 387 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c85 := h 84 (by decide)
  have h8 : Entails.eval a c634 := derived634 a h
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c82 := h 81 (by decide)
  have h11 : Entails.eval a c636 := derived636 a h
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c173 := h 172 (by decide)
  have h14 : Entails.eval a c635 := derived635 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c638 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c608, some c320, some c632, some c393, some c637, some c13, some c201, some c147, some c357, some c464, some c522, some c114, some c89, some c592, some c388, some c629, some c207, some c25, some c156, some c597, some c121, some c389, some c312, some c368, some c60, some c300, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked638 : lratChecker f638 p638 = .success := by decide +kernel
theorem unsat638 : Unsatisfiable (PosFin 57) f638 := by
  apply lratCheckerSound f638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p638
  · intro a ha; simp [p638] at ha; subst a; trivial
  · exact checked638
theorem derived638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c638 := by
  apply localUnsat_implies_entails f638 [c608, c320, c632, c393, c637, c13, c201, c147, c357, c464, c522, c114, c89, c592, c388, c629, c207, c25, c156, c597, c121, c389, c312, c368, c60, c300] c638 unsat638 (by rfl) a
  have h0 : Entails.eval a c608 := derived608 a h
  have h1 : Entails.eval a c320 := h 319 (by decide)
  have h2 : Entails.eval a c632 := derived632 a h
  have h3 : Entails.eval a c393 := h 392 (by decide)
  have h4 : Entails.eval a c637 := derived637 a h
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c464 := derived464 a h
  have h10 : Entails.eval a c522 := derived522 a h
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c592 := derived592 a h
  have h14 : Entails.eval a c388 := h 387 (by decide)
  have h15 : Entails.eval a c629 := derived629 a h
  have h16 : Entails.eval a c207 := h 206 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c156 := h 155 (by decide)
  have h19 : Entails.eval a c597 := derived597 a h
  have h20 : Entails.eval a c121 := h 120 (by decide)
  have h21 : Entails.eval a c389 := h 388 (by decide)
  have h22 : Entails.eval a c312 := h 311 (by decide)
  have h23 : Entails.eval a c368 := h 367 (by decide)
  have h24 : Entails.eval a c60 := h 59 (by decide)
  have h25 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c639 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c632, some c393, some c637, some c13, some c608, some c320, some c592, some c388, some c464, some c201, some c85, some c147, some c71, some c638, some c202, some c160, some c322, some c209, some c128, some c125, some c55, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked639 : lratChecker f639 p639 = .success := by decide +kernel
theorem unsat639 : Unsatisfiable (PosFin 57) f639 := by
  apply lratCheckerSound f639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p639
  · intro a ha; simp [p639] at ha; subst a; trivial
  · exact checked639
theorem derived639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c639 := by
  apply localUnsat_implies_entails f639 [c632, c393, c637, c13, c608, c320, c592, c388, c464, c201, c85, c147, c71, c638, c202, c160, c322, c209, c128, c125, c55] c639 unsat639 (by rfl) a
  have h0 : Entails.eval a c632 := derived632 a h
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c637 := derived637 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c608 := derived608 a h
  have h5 : Entails.eval a c320 := h 319 (by decide)
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c388 := h 387 (by decide)
  have h8 : Entails.eval a c464 := derived464 a h
  have h9 : Entails.eval a c201 := h 200 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c71 := h 70 (by decide)
  have h13 : Entails.eval a c638 := derived638 a h
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c160 := h 159 (by decide)
  have h16 : Entails.eval a c322 := h 321 (by decide)
  have h17 : Entails.eval a c209 := h 208 (by decide)
  have h18 : Entails.eval a c128 := h 127 (by decide)
  have h19 : Entails.eval a c125 := h 124 (by decide)
  have h20 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c640 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨9, by decide⟩, true), (⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨31, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c393, some c13, some c352, some c71, some c162, some c141, some c207, some c208, some c322, some c191, some c160, some c389, some c597, some c189, some c533, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked640 : lratChecker f640 p640 = .success := by decide +kernel
theorem unsat640 : Unsatisfiable (PosFin 57) f640 := by
  apply lratCheckerSound f640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p640
  · intro a ha; simp [p640] at ha; subst a; trivial
  · exact checked640
theorem derived640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c640 := by
  apply localUnsat_implies_entails f640 [c9, c393, c13, c352, c71, c162, c141, c207, c208, c322, c191, c160, c389, c597, c189, c533] c640 unsat640 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c322 := h 321 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c389 := h 388 (by decide)
  have h13 : Entails.eval a c597 := derived597 a h
  have h14 : Entails.eval a c189 := h 188 (by decide)
  have h15 : Entails.eval a c533 := derived533 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c641 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c522, some c388, some c608, some c320, some c632, some c637, some c639, some c640, some c215, some c147, some c268, some c567, some c55, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked641 : lratChecker f641 p641 = .success := by decide +kernel
theorem unsat641 : Unsatisfiable (PosFin 57) f641 := by
  apply lratCheckerSound f641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p641
  · intro a ha; simp [p641] at ha; subst a; trivial
  · exact checked641
theorem derived641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c641 := by
  apply localUnsat_implies_entails f641 [c592, c522, c388, c608, c320, c632, c637, c639, c640, c215, c147, c268, c567, c55] c641 unsat641 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c608 := derived608 a h
  have h4 : Entails.eval a c320 := h 319 (by decide)
  have h5 : Entails.eval a c632 := derived632 a h
  have h6 : Entails.eval a c637 := derived637 a h
  have h7 : Entails.eval a c639 := derived639 a h
  have h8 : Entails.eval a c640 := derived640 a h
  have h9 : Entails.eval a c215 := h 214 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c567 := derived567 a h
  have h13 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c642 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨39, by decide⟩, true), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c393, some c407, some c5, some c318, some c215, some c266, some c577, some c41, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked642 : lratChecker f642 p642 = .success := by decide +kernel
theorem unsat642 : Unsatisfiable (PosFin 57) f642 := by
  apply lratCheckerSound f642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p642
  · intro a ha; simp [p642] at ha; subst a; trivial
  · exact checked642
theorem derived642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c642 := by
  apply localUnsat_implies_entails f642 [c393, c407, c5, c318, c215, c266, c577, c41] c642 unsat642 (by rfl) a
  have h0 : Entails.eval a c393 := h 392 (by decide)
  have h1 : Entails.eval a c407 := derived407 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c215 := h 214 (by decide)
  have h5 : Entails.eval a c266 := h 265 (by decide)
  have h6 : Entails.eval a c577 := derived577 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c643 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c147, some c388, some c592, some c641, some c119, some c85, some c29, some c291, some c9, some c522, some c174, some c90, some c252, some c425, some c122, some c349, some c45, some c165, some c131, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked643 : lratChecker f643 p643 = .success := by decide +kernel
theorem unsat643 : Unsatisfiable (PosFin 57) f643 := by
  apply lratCheckerSound f643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p643
  · intro a ha; simp [p643] at ha; subst a; trivial
  · exact checked643
theorem derived643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c643 := by
  apply localUnsat_implies_entails f643 [c147, c388, c592, c641, c119, c85, c29, c291, c9, c522, c174, c90, c252, c425, c122, c349, c45, c165, c131] c643 unsat643 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c592 := derived592 a h
  have h3 : Entails.eval a c641 := derived641 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c522 := derived522 a h
  have h10 : Entails.eval a c174 := h 173 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c425 := derived425 a h
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c349 := h 348 (by decide)
  have h16 : Entails.eval a c45 := h 44 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c644 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨17, by decide⟩, true), (⟨23, by decide⟩, true), (⟨15, by decide⟩, true), (⟨39, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c641, some c522, some c643, some c14, some c172, some c83, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked644 : lratChecker f644 p644 = .success := by decide +kernel
theorem unsat644 : Unsatisfiable (PosFin 57) f644 := by
  apply lratCheckerSound f644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p644
  · intro a ha; simp [p644] at ha; subst a; trivial
  · exact checked644
theorem derived644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c644 := by
  apply localUnsat_implies_entails f644 [c641, c522, c643, c14, c172, c83] c644 unsat644 (by rfl) a
  have h0 : Entails.eval a c641 := derived641 a h
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c643 := derived643 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c645 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c522, some c641, some c575, some c393, some c592, some c119, some c9, some c642, some c147, some c320, some c318, some c5, some c33, some c266, some c125, some c644, some c216, some c148, some c601, some c47, some c107, some c264, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked645 : lratChecker f645 p645 = .success := by decide +kernel
theorem unsat645 : Unsatisfiable (PosFin 57) f645 := by
  apply lratCheckerSound f645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p645
  · intro a ha; simp [p645] at ha; subst a; trivial
  · exact checked645
theorem derived645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c645 := by
  apply localUnsat_implies_entails f645 [c388, c522, c641, c575, c393, c592, c119, c9, c642, c147, c320, c318, c5, c33, c266, c125, c644, c216, c148, c601, c47, c107, c264] c645 unsat645 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c641 := derived641 a h
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c393 := h 392 (by decide)
  have h5 : Entails.eval a c592 := derived592 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c642 := derived642 a h
  have h9 : Entails.eval a c147 := h 146 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c125 := h 124 (by decide)
  have h16 : Entails.eval a c644 := derived644 a h
  have h17 : Entails.eval a c216 := h 215 (by decide)
  have h18 : Entails.eval a c148 := h 147 (by decide)
  have h19 : Entails.eval a c601 := derived601 a h
  have h20 : Entails.eval a c47 := h 46 (by decide)
  have h21 : Entails.eval a c107 := h 106 (by decide)
  have h22 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c646 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c522, some c641, some c575, some c645, some c355, some c592, some c579, some c79, some c357, some c393, some c148, some c283, some c287, some c610, some c328, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked646 : lratChecker f646 p646 = .success := by decide +kernel
theorem unsat646 : Unsatisfiable (PosFin 57) f646 := by
  apply lratCheckerSound f646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p646
  · intro a ha; simp [p646] at ha; subst a; trivial
  · exact checked646
theorem derived646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c646 := by
  apply localUnsat_implies_entails f646 [c388, c522, c641, c575, c645, c355, c592, c579, c79, c357, c393, c148, c283, c287, c610, c328] c646 unsat646 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c641 := derived641 a h
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c579 := derived579 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c393 := h 392 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c287 := h 286 (by decide)
  have h14 : Entails.eval a c610 := derived610 a h
  have h15 : Entails.eval a c328 := h 327 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c647 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨21, by decide⟩, false), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c388, some c522, some c641, some c579, some c645, some c79, some c357, some c575, some c393, some c119, some c85, some c9, some c125, some c29, some c646, some c320, some c322, some c610, some c160, some c167, some c174, some c628, some c207, some c134, some c90, some c156, some c211, some c122, some c324, some c60, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked647 : lratChecker f647 p647 = .success := by decide +kernel
theorem unsat647 : Unsatisfiable (PosFin 57) f647 := by
  apply lratCheckerSound f647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p647
  · intro a ha; simp [p647] at ha; subst a; trivial
  · exact checked647
theorem derived647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c647 := by
  apply localUnsat_implies_entails f647 [c592, c388, c522, c641, c579, c645, c79, c357, c575, c393, c119, c85, c9, c125, c29, c646, c320, c322, c610, c160, c167, c174, c628, c207, c134, c90, c156, c211, c122, c324, c60] c647 unsat647 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c388 := h 387 (by decide)
  have h2 : Entails.eval a c522 := derived522 a h
  have h3 : Entails.eval a c641 := derived641 a h
  have h4 : Entails.eval a c579 := derived579 a h
  have h5 : Entails.eval a c645 := derived645 a h
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c357 := h 356 (by decide)
  have h8 : Entails.eval a c575 := derived575 a h
  have h9 : Entails.eval a c393 := h 392 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c125 := h 124 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c646 := derived646 a h
  have h16 : Entails.eval a c320 := h 319 (by decide)
  have h17 : Entails.eval a c322 := h 321 (by decide)
  have h18 : Entails.eval a c610 := derived610 a h
  have h19 : Entails.eval a c160 := h 159 (by decide)
  have h20 : Entails.eval a c167 := h 166 (by decide)
  have h21 : Entails.eval a c174 := h 173 (by decide)
  have h22 : Entails.eval a c628 := derived628 a h
  have h23 : Entails.eval a c207 := h 206 (by decide)
  have h24 : Entails.eval a c134 := h 133 (by decide)
  have h25 : Entails.eval a c90 := h 89 (by decide)
  have h26 : Entails.eval a c156 := h 155 (by decide)
  have h27 : Entails.eval a c211 := h 210 (by decide)
  have h28 : Entails.eval a c122 := h 121 (by decide)
  have h29 : Entails.eval a c324 := h 323 (by decide)
  have h30 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c648 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨37, by decide⟩, true), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c575, some c393, some c9, some c5, some c171, some c318, some c607, some c202, some c14, some c160, some c122, some c20, some c204, some c156, some c327, some c325, some c283, some c57, some c322, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true))]
def p648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked648 : lratChecker f648 p648 = .success := by decide +kernel
theorem unsat648 : Unsatisfiable (PosFin 57) f648 := by
  apply lratCheckerSound f648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p648
  · intro a ha; simp [p648] at ha; subst a; trivial
  · exact checked648
theorem derived648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c648 := by
  apply localUnsat_implies_entails f648 [c575, c393, c9, c5, c171, c318, c607, c202, c14, c160, c122, c20, c204, c156, c327, c325, c283, c57, c322] c648 unsat648 (by rfl) a
  have h0 : Entails.eval a c575 := derived575 a h
  have h1 : Entails.eval a c393 := h 392 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c318 := h 317 (by decide)
  have h6 : Entails.eval a c607 := derived607 a h
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c160 := h 159 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c156 := h 155 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c325 := h 324 (by decide)
  have h16 : Entails.eval a c283 := h 282 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c649 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c522, some c641, some c575, some c645, some c355, some c592, some c579, some c79, some c357, some c119, some c85, some c9, some c648, some c173, some c647, some c41, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked649 : lratChecker f649 p649 = .success := by decide +kernel
theorem unsat649 : Unsatisfiable (PosFin 57) f649 := by
  apply lratCheckerSound f649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p649
  · intro a ha; simp [p649] at ha; subst a; trivial
  · exact checked649
theorem derived649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c649 := by
  apply localUnsat_implies_entails f649 [c388, c522, c641, c575, c645, c355, c592, c579, c79, c357, c119, c85, c9, c648, c173, c647, c41] c649 unsat649 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c641 := derived641 a h
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c645 := derived645 a h
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c592 := derived592 a h
  have h7 : Entails.eval a c579 := derived579 a h
  have h8 : Entails.eval a c79 := h 78 (by decide)
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c648 := derived648 a h
  have h14 : Entails.eval a c173 := h 172 (by decide)
  have h15 : Entails.eval a c647 := derived647 a h
  have h16 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c650 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c592, some c641, some c119, some c9, some c522, some c575, some c393, some c645, some c357, some c355, some c649, some c407, some c203, some c171, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked650 : lratChecker f650 p650 = .success := by decide +kernel
theorem unsat650 : Unsatisfiable (PosFin 57) f650 := by
  apply lratCheckerSound f650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p650
  · intro a ha; simp [p650] at ha; subst a; trivial
  · exact checked650
theorem derived650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c650 := by
  apply localUnsat_implies_entails f650 [c388, c592, c641, c119, c9, c522, c575, c393, c645, c357, c355, c649, c407, c203, c171] c650 unsat650 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c592 := derived592 a h
  have h2 : Entails.eval a c641 := derived641 a h
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c522 := derived522 a h
  have h6 : Entails.eval a c575 := derived575 a h
  have h7 : Entails.eval a c393 := h 392 (by decide)
  have h8 : Entails.eval a c645 := derived645 a h
  have h9 : Entails.eval a c357 := h 356 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c649 := derived649 a h
  have h12 : Entails.eval a c407 := derived407 a h
  have h13 : Entails.eval a c203 := h 202 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c651 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c641, some c119, some c388, some c650, some c124, some c106, some c522, some c9, some c85, some c393, some c198, some c174, some c90, some c425, some c389, some c107, some c122, some c202, some c636, some c148, some c80, some c312, some c169, some c2, some c205, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked651 : lratChecker f651 p651 = .success := by decide +kernel
theorem unsat651 : Unsatisfiable (PosFin 57) f651 := by
  apply lratCheckerSound f651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p651
  · intro a ha; simp [p651] at ha; subst a; trivial
  · exact checked651
theorem derived651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c651 := by
  apply localUnsat_implies_entails f651 [c592, c641, c119, c388, c650, c124, c106, c522, c9, c85, c393, c198, c174, c90, c425, c389, c107, c122, c202, c636, c148, c80, c312, c169, c2, c205] c651 unsat651 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c641 := derived641 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c522 := derived522 a h
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  have h10 : Entails.eval a c393 := h 392 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c425 := derived425 a h
  have h15 : Entails.eval a c389 := h 388 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c122 := h 121 (by decide)
  have h18 : Entails.eval a c202 := h 201 (by decide)
  have h19 : Entails.eval a c636 := derived636 a h
  have h20 : Entails.eval a c148 := h 147 (by decide)
  have h21 : Entails.eval a c80 := h 79 (by decide)
  have h22 : Entails.eval a c312 := h 311 (by decide)
  have h23 : Entails.eval a c169 := h 168 (by decide)
  have h24 : Entails.eval a c2 := h 1 (by decide)
  have h25 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c652 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c651, some c357, some c388, some c641, some c522, some c592, some c119, some c9, some c85, some c650, some c124, some c106, some c393, some c198, some c174, some c90, some c425, some c320, some c563, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked652 : lratChecker f652 p652 = .success := by decide +kernel
theorem unsat652 : Unsatisfiable (PosFin 57) f652 := by
  apply lratCheckerSound f652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p652
  · intro a ha; simp [p652] at ha; subst a; trivial
  · exact checked652
theorem derived652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c652 := by
  apply localUnsat_implies_entails f652 [c651, c357, c388, c641, c522, c592, c119, c9, c85, c650, c124, c106, c393, c198, c174, c90, c425, c320, c563] c652 unsat652 (by rfl) a
  have h0 : Entails.eval a c651 := derived651 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c388 := h 387 (by decide)
  have h3 : Entails.eval a c641 := derived641 a h
  have h4 : Entails.eval a c522 := derived522 a h
  have h5 : Entails.eval a c592 := derived592 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c650 := derived650 a h
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c106 := h 105 (by decide)
  have h12 : Entails.eval a c393 := h 392 (by decide)
  have h13 : Entails.eval a c198 := h 197 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c425 := derived425 a h
  have h17 : Entails.eval a c320 := h 319 (by decide)
  have h18 : Entails.eval a c563 := derived563 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c653 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c592, some c641, some c119, some c388, some c650, some c124, some c106, some c393, some c85, some c9, some c522, some c198, some c202, some c174, some c90, some c375, some c425, some c122, some c652, some c159, some c289, some c58, some c57, some c309, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked653 : lratChecker f653 p653 = .success := by decide +kernel
theorem unsat653 : Unsatisfiable (PosFin 57) f653 := by
  apply lratCheckerSound f653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p653
  · intro a ha; simp [p653] at ha; subst a; trivial
  · exact checked653
theorem derived653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c653 := by
  apply localUnsat_implies_entails f653 [c592, c641, c119, c388, c650, c124, c106, c393, c85, c9, c522, c198, c202, c174, c90, c375, c425, c122, c652, c159, c289, c58, c57, c309] c653 unsat653 (by rfl) a
  have h0 : Entails.eval a c592 := derived592 a h
  have h1 : Entails.eval a c641 := derived641 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c388 := h 387 (by decide)
  have h4 : Entails.eval a c650 := derived650 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c393 := h 392 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c522 := derived522 a h
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c174 := h 173 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c375 := h 374 (by decide)
  have h16 : Entails.eval a c425 := derived425 a h
  have h17 : Entails.eval a c122 := h 121 (by decide)
  have h18 : Entails.eval a c652 := derived652 a h
  have h19 : Entails.eval a c159 := h 158 (by decide)
  have h20 : Entails.eval a c289 := h 288 (by decide)
  have h21 : Entails.eval a c58 := h 57 (by decide)
  have h22 : Entails.eval a c57 := h 56 (by decide)
  have h23 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c654 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, true), (⟨50, by decide⟩, false), (⟨14, by decide⟩, true), (⟨46, by decide⟩, false), (⟨15, by decide⟩, true), (⟨45, by decide⟩, true), (⟨13, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, true), (⟨41, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c379, some c3, some c58, some c31, some c290, some c134, some c257, some c160, some c251, some c45, some c321, some c270, some c226, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked654 : lratChecker f654 p654 = .success := by decide +kernel
theorem unsat654 : Unsatisfiable (PosFin 57) f654 := by
  apply lratCheckerSound f654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p654
  · intro a ha; simp [p654] at ha; subst a; trivial
  · exact checked654
theorem derived654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c654 := by
  apply localUnsat_implies_entails f654 [c379, c3, c58, c31, c290, c134, c257, c160, c251, c45, c321, c270, c226] c654 unsat654 (by rfl) a
  have h0 : Entails.eval a c379 := h 378 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c290 := h 289 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c257 := h 256 (by decide)
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c321 := h 320 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c655 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c388, some c522, some c592, some c641, some c119, some c9, some c85, some c650, some c124, some c106, some c393, some c653, some c173, some c201, some c375, some c174, some c14, some c425, some c122, some c654, some c315, some c309, some c160, some c57, some c290, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked655 : lratChecker f655 p655 = .success := by decide +kernel
theorem unsat655 : Unsatisfiable (PosFin 57) f655 := by
  apply lratCheckerSound f655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p655
  · intro a ha; simp [p655] at ha; subst a; trivial
  · exact checked655
theorem derived655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c655 := by
  apply localUnsat_implies_entails f655 [c388, c522, c592, c641, c119, c9, c85, c650, c124, c106, c393, c653, c173, c201, c375, c174, c14, c425, c122, c654, c315, c309, c160, c57, c290] c655 unsat655 (by rfl) a
  have h0 : Entails.eval a c388 := h 387 (by decide)
  have h1 : Entails.eval a c522 := derived522 a h
  have h2 : Entails.eval a c592 := derived592 a h
  have h3 : Entails.eval a c641 := derived641 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c650 := derived650 a h
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c393 := h 392 (by decide)
  have h11 : Entails.eval a c653 := derived653 a h
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c201 := h 200 (by decide)
  have h14 : Entails.eval a c375 := h 374 (by decide)
  have h15 : Entails.eval a c174 := h 173 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c425 := derived425 a h
  have h18 : Entails.eval a c122 := h 121 (by decide)
  have h19 : Entails.eval a c654 := derived654 a h
  have h20 : Entails.eval a c315 := h 314 (by decide)
  have h21 : Entails.eval a c309 := h 308 (by decide)
  have h22 : Entails.eval a c160 := h 159 (by decide)
  have h23 : Entails.eval a c57 := h 56 (by decide)
  have h24 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c656 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c198, some c201, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked656 : lratChecker f656 p656 = .success := by decide +kernel
theorem unsat656 : Unsatisfiable (PosFin 57) f656 := by
  apply lratCheckerSound f656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p656
  · intro a ha; simp [p656] at ha; subst a; trivial
  · exact checked656
theorem derived656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c656 := by
  apply localUnsat_implies_entails f656 [c200, c198, c201] c656 unsat656 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c657 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨49, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c9, some c85, some c656, some c174, some c377, some c375, some c378, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked657 : lratChecker f657 p657 = .success := by decide +kernel
theorem unsat657 : Unsatisfiable (PosFin 57) f657 := by
  apply lratCheckerSound f657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p657
  · intro a ha; simp [p657] at ha; subst a; trivial
  · exact checked657
theorem derived657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c657 := by
  apply localUnsat_implies_entails f657 [c9, c85, c656, c174, c377, c375, c378] c657 unsat657 (by rfl) a
  have h0 : Entails.eval a c9 := h 8 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c656 := derived656 a h
  have h3 : Entails.eval a c174 := h 173 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c375 := h 374 (by decide)
  have h6 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c658 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨41, by decide⟩, false), (⟨53, by decide⟩, true), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c375, some c378, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked658 : lratChecker f658 p658 = .success := by decide +kernel
theorem unsat658 : Unsatisfiable (PosFin 57) f658 := by
  apply lratCheckerSound f658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p658
  · intro a ha; simp [p658] at ha; subst a; trivial
  · exact checked658
theorem derived658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c658 := by
  apply localUnsat_implies_entails f658 [c377, c375, c378] c658 unsat658 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c375 := h 374 (by decide)
  have h2 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c659 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨41, by decide⟩, false), (⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c658, some c379, some c378, some c91, some c119, some c117, some c44, some c114, some c13, some c260, some c30, some c210, some c121, some c75, some c101, some c184, some c4, some c25, some c301, some c146, some c214, some c139, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked659 : lratChecker f659 p659 = .success := by decide +kernel
theorem unsat659 : Unsatisfiable (PosFin 57) f659 := by
  apply lratCheckerSound f659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p659
  · intro a ha; simp [p659] at ha; subst a; trivial
  · exact checked659
theorem derived659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c659 := by
  apply localUnsat_implies_entails f659 [c655, c391, c658, c379, c378, c91, c119, c117, c44, c114, c13, c260, c30, c210, c121, c75, c101, c184, c4, c25, c301, c146, c214, c139] c659 unsat659 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c658 := derived658 a h
  have h3 : Entails.eval a c379 := h 378 (by decide)
  have h4 : Entails.eval a c378 := h 377 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c44 := h 43 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c260 := h 259 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c210 := h 209 (by decide)
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c101 := h 100 (by decide)
  have h17 : Entails.eval a c184 := h 183 (by decide)
  have h18 : Entails.eval a c4 := h 3 (by decide)
  have h19 : Entails.eval a c25 := h 24 (by decide)
  have h20 : Entails.eval a c301 := h 300 (by decide)
  have h21 : Entails.eval a c146 := h 145 (by decide)
  have h22 : Entails.eval a c214 := h 213 (by decide)
  have h23 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c660 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c657, some c658, some c379, some c659, some c89, some c117, some c15, some c91, some c116, some c175, some c118, some c44, some c260, some c30, some c210, some c121, some c75, some c112, some c101, some c389, some c407, some c190, some c198, some c183, some c533, some c185, some c99, some c152, some c149, some c4, some c73, some c327, some c290, some c282, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]]
theorem checked660 : lratChecker f660 p660 = .success := by decide +kernel
theorem unsat660 : Unsatisfiable (PosFin 57) f660 := by
  apply lratCheckerSound f660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p660
  · intro a ha; simp [p660] at ha; subst a; trivial
  · exact checked660
theorem derived660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c660 := by
  apply localUnsat_implies_entails f660 [c655, c391, c657, c658, c379, c659, c89, c117, c15, c91, c116, c175, c118, c44, c260, c30, c210, c121, c75, c112, c101, c389, c407, c190, c198, c183, c533, c185, c99, c152, c149, c4, c73, c327, c290, c282] c660 unsat660 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c657 := derived657 a h
  have h3 : Entails.eval a c658 := derived658 a h
  have h4 : Entails.eval a c379 := h 378 (by decide)
  have h5 : Entails.eval a c659 := derived659 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c91 := h 90 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c175 := h 174 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c112 := h 111 (by decide)
  have h20 : Entails.eval a c101 := h 100 (by decide)
  have h21 : Entails.eval a c389 := h 388 (by decide)
  have h22 : Entails.eval a c407 := derived407 a h
  have h23 : Entails.eval a c190 := h 189 (by decide)
  have h24 : Entails.eval a c198 := h 197 (by decide)
  have h25 : Entails.eval a c183 := h 182 (by decide)
  have h26 : Entails.eval a c533 := derived533 a h
  have h27 : Entails.eval a c185 := h 184 (by decide)
  have h28 : Entails.eval a c99 := h 98 (by decide)
  have h29 : Entails.eval a c152 := h 151 (by decide)
  have h30 : Entails.eval a c149 := h 148 (by decide)
  have h31 : Entails.eval a c4 := h 3 (by decide)
  have h32 : Entails.eval a c73 := h 72 (by decide)
  have h33 : Entails.eval a c327 := h 326 (by decide)
  have h34 : Entails.eval a c290 := h 289 (by decide)
  have h35 : Entails.eval a c282 := h 281 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c661 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c116, some c91, some c15, some c121, some c112, some c533, some c389, some c142, some c367, some c349, some c183, some c11, some c607, some c73, some c167, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked661 : lratChecker f661 p661 = .success := by decide +kernel
theorem unsat661 : Unsatisfiable (PosFin 57) f661 := by
  apply lratCheckerSound f661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p661
  · intro a ha; simp [p661] at ha; subst a; trivial
  · exact checked661
theorem derived661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c661 := by
  apply localUnsat_implies_entails f661 [c655, c391, c116, c91, c15, c121, c112, c533, c389, c142, c367, c349, c183, c11, c607, c73, c167] c661 unsat661 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c91 := h 90 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c121 := h 120 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c533 := derived533 a h
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c367 := h 366 (by decide)
  have h11 : Entails.eval a c349 := h 348 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c11 := h 10 (by decide)
  have h14 : Entails.eval a c607 := derived607 a h
  have h15 : Entails.eval a c73 := h 72 (by decide)
  have h16 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c662 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c91, some c661, some c61, some c2, some c30, some c206, some c260, some c8, some c44, some c304, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked662 : lratChecker f662 p662 = .success := by decide +kernel
theorem unsat662 : Unsatisfiable (PosFin 57) f662 := by
  apply lratCheckerSound f662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p662
  · intro a ha; simp [p662] at ha; subst a; trivial
  · exact checked662
theorem derived662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c662 := by
  apply localUnsat_implies_entails f662 [c655, c91, c661, c61, c2, c30, c206, c260, c8, c44, c304] c662 unsat662 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c661 := derived661 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c663 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c660, some c655, some c391, some c657, some c117, some c15, some c91, some c116, some c118, some c662, some c198, some c208, some c407, some c389, some c368, some c112, some c382, some c123, some c121, some c38, some c23, some c260, some c188, some c44, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked663 : lratChecker f663 p663 = .success := by decide +kernel
theorem unsat663 : Unsatisfiable (PosFin 57) f663 := by
  apply lratCheckerSound f663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p663
  · intro a ha; simp [p663] at ha; subst a; trivial
  · exact checked663
theorem derived663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c663 := by
  apply localUnsat_implies_entails f663 [c660, c655, c391, c657, c117, c15, c91, c116, c118, c662, c198, c208, c407, c389, c368, c112, c382, c123, c121, c38, c23, c260, c188, c44] c663 unsat663 (by rfl) a
  have h0 : Entails.eval a c660 := derived660 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c391 := h 390 (by decide)
  have h3 : Entails.eval a c657 := derived657 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c662 := derived662 a h
  have h10 : Entails.eval a c198 := h 197 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c407 := derived407 a h
  have h13 : Entails.eval a c389 := h 388 (by decide)
  have h14 : Entails.eval a c368 := h 367 (by decide)
  have h15 : Entails.eval a c112 := h 111 (by decide)
  have h16 : Entails.eval a c382 := h 381 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c121 := h 120 (by decide)
  have h19 : Entails.eval a c38 := h 37 (by decide)
  have h20 : Entails.eval a c23 := h 22 (by decide)
  have h21 : Entails.eval a c260 := h 259 (by decide)
  have h22 : Entails.eval a c188 := h 187 (by decide)
  have h23 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c664 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c186, some c367, some c389, some c196, some c368, some c184, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked664 : lratChecker f664 p664 = .success := by decide +kernel
theorem unsat664 : Unsatisfiable (PosFin 57) f664 := by
  apply lratCheckerSound f664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p664
  · intro a ha; simp [p664] at ha; subst a; trivial
  · exact checked664
theorem derived664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c664 := by
  apply localUnsat_implies_entails f664 [c385, c186, c367, c389, c196, c368, c184] c664 unsat664 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c367 := h 366 (by decide)
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c196 := h 195 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c665 : DefaultClause 57 := directClause [(⟨52, by decide⟩, true), (⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c196, some c368, some c184, some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked665 : lratChecker f665 p665 = .success := by decide +kernel
theorem unsat665 : Unsatisfiable (PosFin 57) f665 := by
  apply lratCheckerSound f665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p665
  · intro a ha; simp [p665] at ha; subst a; trivial
  · exact checked665
theorem derived665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c665 := by
  apply localUnsat_implies_entails f665 [c196, c368, c184] c665 unsat665 (by rfl) a
  have h0 : Entails.eval a c196 := h 195 (by decide)
  have h1 : Entails.eval a c368 := h 367 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c666 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c142, some c73, some c349, some c167, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked666 : lratChecker f666 p666 = .success := by decide +kernel
theorem unsat666 : Unsatisfiable (PosFin 57) f666 := by
  apply lratCheckerSound f666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p666
  · intro a ha; simp [p666] at ha; subst a; trivial
  · exact checked666
theorem derived666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c666 := by
  apply localUnsat_implies_entails f666 [c2, c142, c73, c349, c167] c666 unsat666 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c349 := h 348 (by decide)
  have h4 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c667 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨45, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c655, some c200, some c665, some c389, some c367, some c182, some c384, some c190, some c11, some c607, some c666, some c533, some c179, some c121, some c38, some c260, some c258, some c55, some c243, some c125, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked667 : lratChecker f667 p667 = .success := by decide +kernel
theorem unsat667 : Unsatisfiable (PosFin 57) f667 := by
  apply lratCheckerSound f667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p667
  · intro a ha; simp [p667] at ha; subst a; trivial
  · exact checked667
theorem derived667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c667 := by
  apply localUnsat_implies_entails f667 [c391, c655, c200, c665, c389, c367, c182, c384, c190, c11, c607, c666, c533, c179, c121, c38, c260, c258, c55, c243, c125] c667 unsat667 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c665 := derived665 a h
  have h4 : Entails.eval a c389 := h 388 (by decide)
  have h5 : Entails.eval a c367 := h 366 (by decide)
  have h6 : Entails.eval a c182 := h 181 (by decide)
  have h7 : Entails.eval a c384 := h 383 (by decide)
  have h8 : Entails.eval a c190 := h 189 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c607 := derived607 a h
  have h11 : Entails.eval a c666 := derived666 a h
  have h12 : Entails.eval a c533 := derived533 a h
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c121 := h 120 (by decide)
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c260 := h 259 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c55 := h 54 (by decide)
  have h19 : Entails.eval a c243 := h 242 (by decide)
  have h20 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c668 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨6, by decide⟩, false), (⟨56, by decide⟩, false), (⟨45, by decide⟩, false), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨46, by decide⟩, false), (⟨41, by decide⟩, true), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c667, some c201, some c407, some c389, some c191, some c368, some c184, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked668 : lratChecker f668 p668 = .success := by decide +kernel
theorem unsat668 : Unsatisfiable (PosFin 57) f668 := by
  apply lratCheckerSound f668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p668
  · intro a ha; simp [p668] at ha; subst a; trivial
  · exact checked668
theorem derived668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c668 := by
  apply localUnsat_implies_entails f668 [c667, c201, c407, c389, c191, c368, c184] c668 unsat668 (by rfl) a
  have h0 : Entails.eval a c667 := derived667 a h
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c407 := derived407 a h
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c191 := h 190 (by decide)
  have h5 : Entails.eval a c368 := h 367 (by decide)
  have h6 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c669 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c660, some c391, some c663, some c575, some c89, some c114, some c13, some c668, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked669 : lratChecker f669 p669 = .success := by decide +kernel
theorem unsat669 : Unsatisfiable (PosFin 57) f669 := by
  apply lratCheckerSound f669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p669
  · intro a ha; simp [p669] at ha; subst a; trivial
  · exact checked669
theorem derived669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c669 := by
  apply localUnsat_implies_entails f669 [c660, c391, c663, c575, c89, c114, c13, c668] c669 unsat669 (by rfl) a
  have h0 : Entails.eval a c660 := derived660 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c663 := derived663 a h
  have h3 : Entails.eval a c575 := derived575 a h
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c668 := derived668 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c670 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c655, some c657, some c660, some c669, some c90, some c377, some c375, some c118, some c664, some c13, some c198, some c117, some c662, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked670 : lratChecker f670 p670 = .success := by decide +kernel
theorem unsat670 : Unsatisfiable (PosFin 57) f670 := by
  apply lratCheckerSound f670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p670
  · intro a ha; simp [p670] at ha; subst a; trivial
  · exact checked670
theorem derived670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c670 := by
  apply localUnsat_implies_entails f670 [c391, c655, c657, c660, c669, c90, c377, c375, c118, c664, c13, c198, c117, c662] c670 unsat670 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c657 := derived657 a h
  have h3 : Entails.eval a c660 := derived660 a h
  have h4 : Entails.eval a c669 := derived669 a h
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c377 := h 376 (by decide)
  have h7 : Entails.eval a c375 := h 374 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c664 := derived664 a h
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c117 := h 116 (by decide)
  have h13 : Entails.eval a c662 := derived662 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c671 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨51, by decide⟩, false), (⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c121, some c39, some c30, some c257, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked671 : lratChecker f671 p671 = .success := by decide +kernel
theorem unsat671 : Unsatisfiable (PosFin 57) f671 := by
  apply lratCheckerSound f671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p671
  · intro a ha; simp [p671] at ha; subst a; trivial
  · exact checked671
theorem derived671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c671 := by
  apply localUnsat_implies_entails f671 [c123, c121, c39, c30, c257] c671 unsat671 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c672 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨45, by decide⟩, false), (⟨26, by decide⟩, true), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c385, some c371, some c389, some c671, some c112, some c117, some c124, some c94, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked672 : lratChecker f672 p672 = .success := by decide +kernel
theorem unsat672 : Unsatisfiable (PosFin 57) f672 := by
  apply lratCheckerSound f672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p672
  · intro a ha; simp [p672] at ha; subst a; trivial
  · exact checked672
theorem derived672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c672 := by
  apply localUnsat_implies_entails f672 [c377, c385, c371, c389, c671, c112, c117, c124, c94] c672 unsat672 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c385 := h 384 (by decide)
  have h2 : Entails.eval a c371 := h 370 (by decide)
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c671 := derived671 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c117 := h 116 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c673 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c124, some c94, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked673 : lratChecker f673 p673 = .success := by decide +kernel
theorem unsat673 : Unsatisfiable (PosFin 57) f673 := by
  apply lratCheckerSound f673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p673
  · intro a ha; simp [p673] at ha; subst a; trivial
  · exact checked673
theorem derived673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c673 := by
  apply localUnsat_implies_entails f673 [c117, c124, c94] c673 unsat673 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c674 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨43, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c389, some c671, some c112, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked674 : lratChecker f674 p674 = .success := by decide +kernel
theorem unsat674 : Unsatisfiable (PosFin 57) f674 := by
  apply lratCheckerSound f674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p674
  · intro a ha; simp [p674] at ha; subst a; trivial
  · exact checked674
theorem derived674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c674 := by
  apply localUnsat_implies_entails f674 [c389, c671, c112] c674 unsat674 (by rfl) a
  have h0 : Entails.eval a c389 := h 388 (by decide)
  have h1 : Entails.eval a c671 := derived671 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c675 : DefaultClause 57 := directClause [(⟨47, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨45, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c385, some c673, some c15, some c674, some c87, some c123, some c533, some c152, some c2, some c142, some c302, some c73, some c35, some c64, some c327, some c143, some c211, some c135, some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked675 : lratChecker f675 p675 = .success := by decide +kernel
theorem unsat675 : Unsatisfiable (PosFin 57) f675 := by
  apply lratCheckerSound f675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p675
  · intro a ha; simp [p675] at ha; subst a; trivial
  · exact checked675
theorem derived675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c675 := by
  apply localUnsat_implies_entails f675 [c385, c673, c15, c674, c87, c123, c533, c152, c2, c142, c302, c73, c35, c64, c327, c143, c211, c135] c675 unsat675 (by rfl) a
  have h0 : Entails.eval a c385 := h 384 (by decide)
  have h1 : Entails.eval a c673 := derived673 a h
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c674 := derived674 a h
  have h4 : Entails.eval a c87 := h 86 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c533 := derived533 a h
  have h7 : Entails.eval a c152 := h 151 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c302 := h 301 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c327 := h 326 (by decide)
  have h15 : Entails.eval a c143 := h 142 (by decide)
  have h16 : Entails.eval a c211 := h 210 (by decide)
  have h17 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c676 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, true), (⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c675, some c91, some c117, some c673, some c37, some c384, some c256, some c95, some c36, some c121, some c308, some c57, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked676 : lratChecker f676 p676 = .success := by decide +kernel
theorem unsat676 : Unsatisfiable (PosFin 57) f676 := by
  apply lratCheckerSound f676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p676
  · intro a ha; simp [p676] at ha; subst a; trivial
  · exact checked676
theorem derived676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c676 := by
  apply localUnsat_implies_entails f676 [c655, c675, c91, c117, c673, c37, c384, c256, c95, c36, c121, c308, c57] c676 unsat676 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c675 := derived675 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c673 := derived673 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c256 := h 255 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c121 := h 120 (by decide)
  have h11 : Entails.eval a c308 := h 307 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c677 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨45, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c124, some c673, some c110, some c384, some c385, some c389, some c373, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked677 : lratChecker f677 p677 = .success := by decide +kernel
theorem unsat677 : Unsatisfiable (PosFin 57) f677 := by
  apply lratCheckerSound f677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p677
  · intro a ha; simp [p677] at ha; subst a; trivial
  · exact checked677
theorem derived677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c677 := by
  apply localUnsat_implies_entails f677 [c116, c124, c673, c110, c384, c385, c389, c373] c677 unsat677 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c124 := h 123 (by decide)
  have h2 : Entails.eval a c673 := derived673 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c384 := h 383 (by decide)
  have h5 : Entails.eval a c385 := h 384 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c678 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨14, by decide⟩, false), (⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c655, some c677, some c672, some c676, some c122, some c118, some c2, some c93, some c179, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked678 : lratChecker f678 p678 = .success := by decide +kernel
theorem unsat678 : Unsatisfiable (PosFin 57) f678 := by
  apply lratCheckerSound f678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p678
  · intro a ha; simp [p678] at ha; subst a; trivial
  · exact checked678
theorem derived678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c678 := by
  apply localUnsat_implies_entails f678 [c391, c655, c677, c672, c676, c122, c118, c2, c93, c179] c678 unsat678 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c677 := derived677 a h
  have h3 : Entails.eval a c672 := derived672 a h
  have h4 : Entails.eval a c676 := derived676 a h
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c679 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨45, by decide⟩, false), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c670, some c391, some c655, some c13, some c198, some c678, some c658, some c659, some c174, some c1, some c308, some c289, some c159, some c152, some c206, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked679 : lratChecker f679 p679 = .success := by decide +kernel
theorem unsat679 : Unsatisfiable (PosFin 57) f679 := by
  apply lratCheckerSound f679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p679
  · intro a ha; simp [p679] at ha; subst a; trivial
  · exact checked679
theorem derived679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c679 := by
  apply localUnsat_implies_entails f679 [c670, c391, c655, c13, c198, c678, c658, c659, c174, c1, c308, c289, c159, c152, c206] c679 unsat679 (by rfl) a
  have h0 : Entails.eval a c670 := derived670 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c13 := h 12 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c678 := derived678 a h
  have h6 : Entails.eval a c658 := derived658 a h
  have h7 : Entails.eval a c659 := derived659 a h
  have h8 : Entails.eval a c174 := h 173 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c308 := h 307 (by decide)
  have h11 : Entails.eval a c289 := h 288 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c680 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨5, by decide⟩, false), (⟨45, by decide⟩, false), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c679, some c655, some c659, some c378, some c173, some c91, some c124, some c18, some c207, some c208, some c182, some c196, some c87, some c389, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked680 : lratChecker f680 p680 = .success := by decide +kernel
theorem unsat680 : Unsatisfiable (PosFin 57) f680 := by
  apply lratCheckerSound f680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p680
  · intro a ha; simp [p680] at ha; subst a; trivial
  · exact checked680
theorem derived680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c680 := by
  apply localUnsat_implies_entails f680 [c679, c655, c659, c378, c173, c91, c124, c18, c207, c208, c182, c196, c87, c389] c680 unsat680 (by rfl) a
  have h0 : Entails.eval a c679 := derived679 a h
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c659 := derived659 a h
  have h3 : Entails.eval a c378 := h 377 (by decide)
  have h4 : Entails.eval a c173 := h 172 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c207 := h 206 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c182 := h 181 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c681 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨46, by decide⟩, false), (⟨6, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨54, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c37, some c256, some c655, some c1, some c308, some c36, some c122, some c2, some c93, some c382, some c179, some c95, some c200, some c123, some c208, some c18, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked681 : lratChecker f681 p681 = .success := by decide +kernel
theorem unsat681 : Unsatisfiable (PosFin 57) f681 := by
  apply lratCheckerSound f681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p681
  · intro a ha; simp [p681] at ha; subst a; trivial
  · exact checked681
theorem derived681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c681 := by
  apply localUnsat_implies_entails f681 [c37, c256, c655, c1, c308, c36, c122, c2, c93, c382, c179, c95, c200, c123, c208, c18] c681 unsat681 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c256 := h 255 (by decide)
  have h2 : Entails.eval a c655 := derived655 a h
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c308 := h 307 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c93 := h 92 (by decide)
  have h9 : Entails.eval a c382 := h 381 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c200 := h 199 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  have h14 : Entails.eval a c208 := h 207 (by decide)
  have h15 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c682 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨41, by decide⟩, true), (⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c673, some c182, some c384, some c385, some c11, some c373, some c389, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked682 : lratChecker f682 p682 = .success := by decide +kernel
theorem unsat682 : Unsatisfiable (PosFin 57) f682 := by
  apply lratCheckerSound f682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p682
  · intro a ha; simp [p682] at ha; subst a; trivial
  · exact checked682
theorem derived682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c682 := by
  apply localUnsat_implies_entails f682 [c124, c673, c182, c384, c385, c11, c373, c389] c682 unsat682 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c673 := derived673 a h
  have h2 : Entails.eval a c182 := h 181 (by decide)
  have h3 : Entails.eval a c384 := h 383 (by decide)
  have h4 : Entails.eval a c385 := h 384 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c373 := h 372 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c683 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c91, some c186, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked683 : lratChecker f683 p683 = .success := by decide +kernel
theorem unsat683 : Unsatisfiable (PosFin 57) f683 := by
  apply lratCheckerSound f683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p683
  · intro a ha; simp [p683] at ha; subst a; trivial
  · exact checked683
theorem derived683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c683 := by
  apply localUnsat_implies_entails f683 [c15, c91, c186] c683 unsat683 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c684 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨45, by decide⟩, false), (⟨26, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c679, some c683, some c680, some c682, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked684 : lratChecker f684 p684 = .success := by decide +kernel
theorem unsat684 : Unsatisfiable (PosFin 57) f684 := by
  apply lratCheckerSound f684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p684
  · intro a ha; simp [p684] at ha; subst a; trivial
  · exact checked684
theorem derived684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c684 := by
  apply localUnsat_implies_entails f684 [c655, c679, c683, c680, c682] c684 unsat684 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c679 := derived679 a h
  have h2 : Entails.eval a c683 := derived683 a h
  have h3 : Entails.eval a c680 := derived680 a h
  have h4 : Entails.eval a c682 := derived682 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c685 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c186, some c11, some c389, some c373, some c184, some c384, some c12, some c39, some c121, some c257, some c30, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked685 : lratChecker f685 p685 = .success := by decide +kernel
theorem unsat685 : Unsatisfiable (PosFin 57) f685 := by
  apply lratCheckerSound f685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p685
  · intro a ha; simp [p685] at ha; subst a; trivial
  · exact checked685
theorem derived685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c685 := by
  apply localUnsat_implies_entails f685 [c208, c186, c11, c389, c373, c184, c384, c12, c39, c121, c257, c30] c685 unsat685 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c186 := h 185 (by decide)
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c373 := h 372 (by decide)
  have h5 : Entails.eval a c184 := h 183 (by decide)
  have h6 : Entails.eval a c384 := h 383 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c39 := h 38 (by decide)
  have h9 : Entails.eval a c121 := h 120 (by decide)
  have h10 : Entails.eval a c257 := h 256 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c686 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨42, by decide⟩, true), (⟨12, by decide⟩, true), (⟨44, by decide⟩, false), (⟨9, by decide⟩, true), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c60, some c93, some c260, some c300, some c118, some c36, some c151, some c308, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked686 : lratChecker f686 p686 = .success := by decide +kernel
theorem unsat686 : Unsatisfiable (PosFin 57) f686 := by
  apply lratCheckerSound f686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p686
  · intro a ha; simp [p686] at ha; subst a; trivial
  · exact checked686
theorem derived686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c686 := by
  apply localUnsat_implies_entails f686 [c30, c60, c93, c260, c300, c118, c36, c151, c308] c686 unsat686 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c260 := h 259 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c151 := h 150 (by decide)
  have h8 : Entails.eval a c308 := h 307 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c687 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨15, by decide⟩, false), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c186, some c377, some c208, some c201, some c683, some c184, some c382, some c686, some c122, some c121, some c12, some c19, some c4, some c25, some c389, some c300, some c194, some c436, some c206, some c308, some c149, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked687 : lratChecker f687 p687 = .success := by decide +kernel
theorem unsat687 : Unsatisfiable (PosFin 57) f687 := by
  apply lratCheckerSound f687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p687
  · intro a ha; simp [p687] at ha; subst a; trivial
  · exact checked687
theorem derived687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c687 := by
  apply localUnsat_implies_entails f687 [c655, c391, c186, c377, c208, c201, c683, c184, c382, c686, c122, c121, c12, c19, c4, c25, c389, c300, c194, c436, c206, c308, c149] c687 unsat687 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c377 := h 376 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c683 := derived683 a h
  have h7 : Entails.eval a c184 := h 183 (by decide)
  have h8 : Entails.eval a c382 := h 381 (by decide)
  have h9 : Entails.eval a c686 := derived686 a h
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c4 := h 3 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c389 := h 388 (by decide)
  have h17 : Entails.eval a c300 := h 299 (by decide)
  have h18 : Entails.eval a c194 := h 193 (by decide)
  have h19 : Entails.eval a c436 := derived436 a h
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c308 := h 307 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c688 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨14, by decide⟩, false), (⟨44, by decide⟩, true), (⟨3, by decide⟩, false), (⟨46, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c122, some c121, some c101, some c533, some c187, some c666, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked688 : lratChecker f688 p688 = .success := by decide +kernel
theorem unsat688 : Unsatisfiable (PosFin 57) f688 := by
  apply lratCheckerSound f688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p688
  · intro a ha; simp [p688] at ha; subst a; trivial
  · exact checked688
theorem derived688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c688 := by
  apply localUnsat_implies_entails f688 [c122, c121, c101, c533, c187, c666] c688 unsat688 (by rfl) a
  have h0 : Entails.eval a c122 := h 121 (by decide)
  have h1 : Entails.eval a c121 := h 120 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c533 := derived533 a h
  have h4 : Entails.eval a c187 := h 186 (by decide)
  have h5 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c689 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f689 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c391, some c655, some c186, some c208, some c377, some c685, some c687, some c373, some c389, some c194, some c688, some c2, some c30, some c179, some c260, some c258, some c93, some c248, some c118, some c138, some c55, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p689 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked689 : lratChecker f689 p689 = .success := by decide +kernel
theorem unsat689 : Unsatisfiable (PosFin 57) f689 := by
  apply lratCheckerSound f689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p689
  · intro a ha; simp [p689] at ha; subst a; trivial
  · exact checked689
theorem derived689 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c689 := by
  apply localUnsat_implies_entails f689 [c391, c655, c186, c208, c377, c685, c687, c373, c389, c194, c688, c2, c30, c179, c260, c258, c93, c248, c118, c138, c55] c689 unsat689 (by rfl) a
  have h0 : Entails.eval a c391 := h 390 (by decide)
  have h1 : Entails.eval a c655 := derived655 a h
  have h2 : Entails.eval a c186 := h 185 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c377 := h 376 (by decide)
  have h5 : Entails.eval a c685 := derived685 a h
  have h6 : Entails.eval a c687 := derived687 a h
  have h7 : Entails.eval a c373 := h 372 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c688 := derived688 a h
  have h11 : Entails.eval a c2 := h 1 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c179 := h 178 (by decide)
  have h14 : Entails.eval a c260 := h 259 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  have h16 : Entails.eval a c93 := h 92 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c118 := h 117 (by decide)
  have h19 : Entails.eval a c138 := h 137 (by decide)
  have h20 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c690 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨17, by decide⟩, false), (⟨48, by decide⟩, false), (⟨22, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨14, by decide⟩, false), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨49, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f690 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c179, some c93, some c118, some c8, some c55, some c308, some c303, some c125, some c141, some c214, some c70, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p690 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked690 : lratChecker f690 p690 = .success := by decide +kernel
theorem unsat690 : Unsatisfiable (PosFin 57) f690 := by
  apply lratCheckerSound f690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p690
  · intro a ha; simp [p690] at ha; subst a; trivial
  · exact checked690
theorem derived690 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c690 := by
  apply localUnsat_implies_entails f690 [c206, c179, c93, c118, c8, c55, c308, c303, c125, c141, c214, c70] c690 unsat690 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c179 := h 178 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c308 := h 307 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c214 := h 213 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c691 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f691 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c689, some c200, some c2, some c30, some c205, some c260, some c131, some c196, some c389, some c258, some c249, some c243, some c690, some c377, some c371, some c385, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p691 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked691 : lratChecker f691 p691 = .success := by decide +kernel
theorem unsat691 : Unsatisfiable (PosFin 57) f691 := by
  apply lratCheckerSound f691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p691
  · intro a ha; simp [p691] at ha; subst a; trivial
  · exact checked691
theorem derived691 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c691 := by
  apply localUnsat_implies_entails f691 [c655, c391, c689, c200, c2, c30, c205, c260, c131, c196, c389, c258, c249, c243, c690, c377, c371, c385] c691 unsat691 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c196 := h 195 (by decide)
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c258 := h 257 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c243 := h 242 (by decide)
  have h14 : Entails.eval a c690 := derived690 a h
  have h15 : Entails.eval a c377 := h 376 (by decide)
  have h16 : Entails.eval a c371 := h 370 (by decide)
  have h17 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c692 : DefaultClause 57 := directClause [(⟨46, by decide⟩, true), (⟨51, by decide⟩, true), (⟨45, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f692 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c377, some c371, some c385, some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p692 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked692 : lratChecker f692 p692 = .success := by decide +kernel
theorem unsat692 : Unsatisfiable (PosFin 57) f692 := by
  apply lratCheckerSound f692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p692
  · intro a ha; simp [p692] at ha; subst a; trivial
  · exact checked692
theorem derived692 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c692 := by
  apply localUnsat_implies_entails f692 [c377, c371, c385] c692 unsat692 (by rfl) a
  have h0 : Entails.eval a c377 := h 376 (by decide)
  have h1 : Entails.eval a c371 := h 370 (by decide)
  have h2 : Entails.eval a c385 := h 384 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c693 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨41, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false), (⟨45, by decide⟩, false), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨50, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f693 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c655, some c391, some c689, some c200, some c691, some c122, some c121, some c88, some c101, some c40, some c389, some c258, some c692, some c383, some c187, some c241, some c25, some c256, some c136, some c55, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p693 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked693 : lratChecker f693 p693 = .success := by decide +kernel
theorem unsat693 : Unsatisfiable (PosFin 57) f693 := by
  apply lratCheckerSound f693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p693
  · intro a ha; simp [p693] at ha; subst a; trivial
  · exact checked693
theorem derived693 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c693 := by
  apply localUnsat_implies_entails f693 [c655, c391, c689, c200, c691, c122, c121, c88, c101, c40, c389, c258, c692, c383, c187, c241, c25, c256, c136, c55] c693 unsat693 (by rfl) a
  have h0 : Entails.eval a c655 := derived655 a h
  have h1 : Entails.eval a c391 := h 390 (by decide)
  have h2 : Entails.eval a c689 := derived689 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c122 := h 121 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c258 := h 257 (by decide)
  have h12 : Entails.eval a c692 := derived692 a h
  have h13 : Entails.eval a c383 := h 382 (by decide)
  have h14 : Entails.eval a c187 := h 186 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c256 := h 255 (by decide)
  have h18 : Entails.eval a c136 := h 135 (by decide)
  have h19 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived693

end CochromaticTwenty.Certificates.B16_1_2
