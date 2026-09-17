import MerLeanExperiment.Certificates.B16_4_2.Steps1100_1199

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1584 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, false), (⟨33, by decide⟩, false), (⟨38, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c74, some c102, some c337, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1584 : lratChecker f1584 p1584 = .success := by decide +kernel
theorem unsat1584 : Unsatisfiable (PosFin 57) f1584 := by
  apply lratCheckerSound f1584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1584
  · intro a ha; simp [p1584] at ha; subst a; trivial
  · exact checked1584
theorem derived1584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1584 := by
  apply localUnsat_implies_entails f1584 [c74, c102, c337] c1584 unsat1584 (by rfl) a
  have h0 : Entails.eval a c74 := h 73 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1585 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1577, some c631, some c22, some c42, some c210, some c141, some c45, some c250, some c1584, some c251, some c104, some c265, some c1583, some c1580, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1585 : lratChecker f1585 p1585 = .success := by decide +kernel
theorem unsat1585 : Unsatisfiable (PosFin 57) f1585 := by
  apply lratCheckerSound f1585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1585
  · intro a ha; simp [p1585] at ha; subst a; trivial
  · exact checked1585
theorem derived1585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1585 := by
  apply localUnsat_implies_entails f1585 [c1569, c1577, c631, c22, c42, c210, c141, c45, c250, c1584, c251, c104, c265, c1583, c1580] c1585 unsat1585 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1577 := derived1577 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c250 := h 249 (by decide)
  have h9 : Entails.eval a c1584 := derived1584 a h
  have h10 : Entails.eval a c251 := h 250 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c1583 := derived1583 a h
  have h14 : Entails.eval a c1580 := derived1580 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1586 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1577, some c22, some c631, some c42, some c210, some c45, some c250, some c251, some c141, some c54, some c98, some c1578, some c355, some c340, some c1585, some c31, some c52, some c219, some c318, some c277, some c305, some c341, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1586 : lratChecker f1586 p1586 = .success := by decide +kernel
theorem unsat1586 : Unsatisfiable (PosFin 57) f1586 := by
  apply lratCheckerSound f1586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1586
  · intro a ha; simp [p1586] at ha; subst a; trivial
  · exact checked1586
theorem derived1586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1586 := by
  apply localUnsat_implies_entails f1586 [c1569, c1577, c22, c631, c42, c210, c45, c250, c251, c141, c54, c98, c1578, c355, c340, c1585, c31, c52, c219, c318, c277, c305, c341] c1586 unsat1586 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1577 := derived1577 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c250 := h 249 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  have h10 : Entails.eval a c54 := h 53 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c1578 := derived1578 a h
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c340 := h 339 (by decide)
  have h15 : Entails.eval a c1585 := derived1585 a h
  have h16 : Entails.eval a c31 := h 30 (by decide)
  have h17 : Entails.eval a c52 := h 51 (by decide)
  have h18 : Entails.eval a c219 := h 218 (by decide)
  have h19 : Entails.eval a c318 := h 317 (by decide)
  have h20 : Entails.eval a c277 := h 276 (by decide)
  have h21 : Entails.eval a c305 := h 304 (by decide)
  have h22 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1587 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1577, some c22, some c42, some c210, some c141, some c45, some c251, some c250, some c104, some c1584, some c1586, some c112, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1587 : lratChecker f1587 p1587 = .success := by decide +kernel
theorem unsat1587 : Unsatisfiable (PosFin 57) f1587 := by
  apply lratCheckerSound f1587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1587
  · intro a ha; simp [p1587] at ha; subst a; trivial
  · exact checked1587
theorem derived1587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1587 := by
  apply localUnsat_implies_entails f1587 [c1569, c631, c1577, c22, c42, c210, c141, c45, c251, c250, c104, c1584, c1586, c112] c1587 unsat1587 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1577 := derived1577 a h
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c1584 := derived1584 a h
  have h12 : Entails.eval a c1586 := derived1586 a h
  have h13 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1588 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c211, some c141, some c45, some c53, some c54, some c354, some c338, some c316, some c320, some c1092, some c359, some c337, some c281, some c310, some c318, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1588 : lratChecker f1588 p1588 = .success := by decide +kernel
theorem unsat1588 : Unsatisfiable (PosFin 57) f1588 := by
  apply lratCheckerSound f1588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1588
  · intro a ha; simp [p1588] at ha; subst a; trivial
  · exact checked1588
theorem derived1588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1588 := by
  apply localUnsat_implies_entails f1588 [c1569, c631, c211, c141, c45, c53, c54, c354, c338, c316, c320, c1092, c359, c337, c281, c310, c318] c1588 unsat1588 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c45 := h 44 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c338 := h 337 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c1092 := derived1092 a h
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c337 := h 336 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  have h15 : Entails.eval a c310 := h 309 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1589 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c120, some c1092, some c16, some c813, some c147, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1589 : lratChecker f1589 p1589 = .success := by decide +kernel
theorem unsat1589 : Unsatisfiable (PosFin 57) f1589 := by
  apply lratCheckerSound f1589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1589
  · intro a ha; simp [p1589] at ha; subst a; trivial
  · exact checked1589
theorem derived1589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1589 := by
  apply localUnsat_implies_entails f1589 [c1569, c120, c1092, c16, c813, c147] c1589 unsat1589 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c1092 := derived1092 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1590 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c358, some c354, some c65, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1590 : lratChecker f1590 p1590 = .success := by decide +kernel
theorem unsat1590 : Unsatisfiable (PosFin 57) f1590 := by
  apply lratCheckerSound f1590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1590
  · intro a ha; simp [p1590] at ha; subst a; trivial
  · exact checked1590
theorem derived1590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1590 := by
  apply localUnsat_implies_entails f1590 [c1569, c358, c354, c65] c1590 unsat1590 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1591 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1282, some c631, some c1588, some c1572, some c1590, some c24, some c1589, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1591 : lratChecker f1591 p1591 = .success := by decide +kernel
theorem unsat1591 : Unsatisfiable (PosFin 57) f1591 := by
  apply lratCheckerSound f1591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1591
  · intro a ha; simp [p1591] at ha; subst a; trivial
  · exact checked1591
theorem derived1591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1591 := by
  apply localUnsat_implies_entails f1591 [c1587, c1282, c631, c1588, c1572, c1590, c24, c1589] c1591 unsat1591 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1588 := derived1588 a h
  have h4 : Entails.eval a c1572 := derived1572 a h
  have h5 : Entails.eval a c1590 := derived1590 a h
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c1589 := derived1589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1592 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨38, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1282, some c631, some c265, some c211, some c141, some c45, some c53, some c54, some c316, some c320, some c55, some c151, some c13, some c118, some c146, some c773, some c318, some c215, some c356, some c28, some c281, some c12, some c340, some c117, some c311, some c337, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1592 : lratChecker f1592 p1592 = .success := by decide +kernel
theorem unsat1592 : Unsatisfiable (PosFin 57) f1592 := by
  apply lratCheckerSound f1592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1592
  · intro a ha; simp [p1592] at ha; subst a; trivial
  · exact checked1592
theorem derived1592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1592 := by
  apply localUnsat_implies_entails f1592 [c1569, c1282, c631, c265, c211, c141, c45, c53, c54, c316, c320, c55, c151, c13, c118, c146, c773, c318, c215, c356, c28, c281, c12, c340, c117, c311, c337] c1592 unsat1592 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c320 := h 319 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c151 := h 150 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c773 := derived773 a h
  have h17 : Entails.eval a c318 := h 317 (by decide)
  have h18 : Entails.eval a c215 := h 214 (by decide)
  have h19 : Entails.eval a c356 := h 355 (by decide)
  have h20 : Entails.eval a c28 := h 27 (by decide)
  have h21 : Entails.eval a c281 := h 280 (by decide)
  have h22 : Entails.eval a c12 := h 11 (by decide)
  have h23 : Entails.eval a c340 := h 339 (by decide)
  have h24 : Entails.eval a c117 := h 116 (by decide)
  have h25 : Entails.eval a c311 := h 310 (by decide)
  have h26 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1593 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c1589, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1593 : lratChecker f1593 p1593 = .success := by decide +kernel
theorem unsat1593 : Unsatisfiable (PosFin 57) f1593 := by
  apply lratCheckerSound f1593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1593
  · intro a ha; simp [p1593] at ha; subst a; trivial
  · exact checked1593
theorem derived1593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1593 := by
  apply localUnsat_implies_entails f1593 [c24, c1589] c1593 unsat1593 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c1589 := derived1589 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1594 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1587, some c1591, some c1592, some c1572, some c1593, some c1282, some c265, some c355, some c284, some c147, some c16, some c1580, some c128, some c139, some c21, some c91, some c324, some c208, some c359, some c174, some c280, some c330, some c317, some c246, some c53, some c210, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1594 : lratChecker f1594 p1594 = .success := by decide +kernel
theorem unsat1594 : Unsatisfiable (PosFin 57) f1594 := by
  apply lratCheckerSound f1594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1594
  · intro a ha; simp [p1594] at ha; subst a; trivial
  · exact checked1594
theorem derived1594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1594 := by
  apply localUnsat_implies_entails f1594 [c1569, c631, c1587, c1591, c1592, c1572, c1593, c1282, c265, c355, c284, c147, c16, c1580, c128, c139, c21, c91, c324, c208, c359, c174, c280, c330, c317, c246, c53, c210] c1594 unsat1594 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1591 := derived1591 a h
  have h4 : Entails.eval a c1592 := derived1592 a h
  have h5 : Entails.eval a c1572 := derived1572 a h
  have h6 : Entails.eval a c1593 := derived1593 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c355 := h 354 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c1580 := derived1580 a h
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c139 := h 138 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c91 := h 90 (by decide)
  have h18 : Entails.eval a c324 := h 323 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c359 := h 358 (by decide)
  have h21 : Entails.eval a c174 := h 173 (by decide)
  have h22 : Entails.eval a c280 := h 279 (by decide)
  have h23 : Entails.eval a c330 := h 329 (by decide)
  have h24 : Entails.eval a c317 := h 316 (by decide)
  have h25 : Entails.eval a c246 := h 245 (by decide)
  have h26 : Entails.eval a c53 := h 52 (by decide)
  have h27 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1595 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨38, by decide⟩, true), (⟨6, by decide⟩, false), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1282, some c631, some c37, some c65, some c356, some c67, some c163, some c13, some c118, some c146, some c210, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1595 : lratChecker f1595 p1595 = .success := by decide +kernel
theorem unsat1595 : Unsatisfiable (PosFin 57) f1595 := by
  apply lratCheckerSound f1595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1595
  · intro a ha; simp [p1595] at ha; subst a; trivial
  · exact checked1595
theorem derived1595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1595 := by
  apply localUnsat_implies_entails f1595 [c1569, c1282, c631, c37, c65, c356, c67, c163, c13, c118, c146, c210] c1595 unsat1595 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1596 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1587, some c1282, some c631, some c265, some c1591, some c1592, some c1572, some c1593, some c1595, some c355, some c1594, some c284, some c147, some c35, some c14, some c117, some c359, some c384, some c280, some c317, some c53, some c46, some c1278, some c344, some c52, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1596 : lratChecker f1596 p1596 = .success := by decide +kernel
theorem unsat1596 : Unsatisfiable (PosFin 57) f1596 := by
  apply lratCheckerSound f1596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1596
  · intro a ha; simp [p1596] at ha; subst a; trivial
  · exact checked1596
theorem derived1596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1596 := by
  apply localUnsat_implies_entails f1596 [c1569, c1587, c1282, c631, c265, c1591, c1592, c1572, c1593, c1595, c355, c1594, c284, c147, c35, c14, c117, c359, c384, c280, c317, c53, c46, c1278, c344, c52] c1596 unsat1596 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c265 := h 264 (by decide)
  have h5 : Entails.eval a c1591 := derived1591 a h
  have h6 : Entails.eval a c1592 := derived1592 a h
  have h7 : Entails.eval a c1572 := derived1572 a h
  have h8 : Entails.eval a c1593 := derived1593 a h
  have h9 : Entails.eval a c1595 := derived1595 a h
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c1594 := derived1594 a h
  have h12 : Entails.eval a c284 := h 283 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c117 := h 116 (by decide)
  have h17 : Entails.eval a c359 := h 358 (by decide)
  have h18 : Entails.eval a c384 := derived384 a h
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c53 := h 52 (by decide)
  have h22 : Entails.eval a c46 := h 45 (by decide)
  have h23 : Entails.eval a c1278 := derived1278 a h
  have h24 : Entails.eval a c344 := h 343 (by decide)
  have h25 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1597 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨20, by decide⟩, false), (⟨40, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c15, some c268, some c269, some c430, some c126, some c91, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1597 : lratChecker f1597 p1597 = .success := by decide +kernel
theorem unsat1597 : Unsatisfiable (PosFin 57) f1597 := by
  apply lratCheckerSound f1597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1597
  · intro a ha; simp [p1597] at ha; subst a; trivial
  · exact checked1597
theorem derived1597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1597 := by
  apply localUnsat_implies_entails f1597 [c120, c15, c268, c269, c430, c126, c91] c1597 unsat1597 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c430 := derived430 a h
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1598 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c356, some c1282, some c233, some c1597, some c1461, some c28, some c112, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1598 : lratChecker f1598 p1598 = .success := by decide +kernel
theorem unsat1598 : Unsatisfiable (PosFin 57) f1598 := by
  apply lratCheckerSound f1598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1598
  · intro a ha; simp [p1598] at ha; subst a; trivial
  · exact checked1598
theorem derived1598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1598 := by
  apply localUnsat_implies_entails f1598 [c1077, c356, c1282, c233, c1597, c1461, c28, c112] c1598 unsat1598 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c1597 := derived1597 a h
  have h5 : Entails.eval a c1461 := derived1461 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1599 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c265, some c72, some c43, some c111, some c211, some c21, some c28, some c45, some c53, some c337, some c1015, some c49, some c150, some c320, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1599 : lratChecker f1599 p1599 = .success := by decide +kernel
theorem unsat1599 : Unsatisfiable (PosFin 57) f1599 := by
  apply lratCheckerSound f1599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1599
  · intro a ha; simp [p1599] at ha; subst a; trivial
  · exact checked1599
theorem derived1599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1599 := by
  apply localUnsat_implies_entails f1599 [c1569, c631, c265, c72, c43, c111, c211, c21, c28, c45, c53, c337, c1015, c49, c150, c320] c1599 unsat1599 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c337 := h 336 (by decide)
  have h12 : Entails.eval a c1015 := derived1015 a h
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c150 := h 149 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1600 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨5, by decide⟩, true), (⟨33, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c265, some c28, some c21, some c211, some c45, some c53, some c337, some c1015, some c49, some c150, some c320, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1600 : lratChecker f1600 p1600 = .success := by decide +kernel
theorem unsat1600 : Unsatisfiable (PosFin 57) f1600 := by
  apply lratCheckerSound f1600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1600
  · intro a ha; simp [p1600] at ha; subst a; trivial
  · exact checked1600
theorem derived1600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1600 := by
  apply localUnsat_implies_entails f1600 [c1569, c631, c265, c28, c21, c211, c45, c53, c337, c1015, c49, c150, c320] c1600 unsat1600 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c211 := h 210 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c337 := h 336 (by decide)
  have h9 : Entails.eval a c1015 := derived1015 a h
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c150 := h 149 (by decide)
  have h12 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1601 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c265, some c1587, some c1282, some c1596, some c1077, some c1495, some c356, some c1598, some c358, some c1595, some c355, some c1599, some c112, some c1600, some c702, some c147, some c280, some c284, some c16, some c317, some c53, some c56, some c1278, some c319, some c155, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1601 : lratChecker f1601 p1601 = .success := by decide +kernel
theorem unsat1601 : Unsatisfiable (PosFin 57) f1601 := by
  apply lratCheckerSound f1601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1601
  · intro a ha; simp [p1601] at ha; subst a; trivial
  · exact checked1601
theorem derived1601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1601 := by
  apply localUnsat_implies_entails f1601 [c1569, c631, c265, c1587, c1282, c1596, c1077, c1495, c356, c1598, c358, c1595, c355, c1599, c112, c1600, c702, c147, c280, c284, c16, c317, c53, c56, c1278, c319, c155] c1601 unsat1601 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1596 := derived1596 a h
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c1495 := derived1495 a h
  have h8 : Entails.eval a c356 := h 355 (by decide)
  have h9 : Entails.eval a c1598 := derived1598 a h
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c1595 := derived1595 a h
  have h12 : Entails.eval a c355 := h 354 (by decide)
  have h13 : Entails.eval a c1599 := derived1599 a h
  have h14 : Entails.eval a c112 := h 111 (by decide)
  have h15 : Entails.eval a c1600 := derived1600 a h
  have h16 : Entails.eval a c702 := derived702 a h
  have h17 : Entails.eval a c147 := h 146 (by decide)
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c16 := h 15 (by decide)
  have h21 : Entails.eval a c317 := h 316 (by decide)
  have h22 : Entails.eval a c53 := h 52 (by decide)
  have h23 : Entails.eval a c56 := h 55 (by decide)
  have h24 : Entails.eval a c1278 := derived1278 a h
  have h25 : Entails.eval a c319 := h 318 (by decide)
  have h26 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1602 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c120, some c235, some c8, some c1418, some c1427, some c233, some c271, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1602 : lratChecker f1602 p1602 = .success := by decide +kernel
theorem unsat1602 : Unsatisfiable (PosFin 57) f1602 := by
  apply lratCheckerSound f1602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1602
  · intro a ha; simp [p1602] at ha; subst a; trivial
  · exact checked1602
theorem derived1602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1602 := by
  apply localUnsat_implies_entails f1602 [c24, c120, c235, c8, c1418, c1427, c233, c271] c1602 unsat1602 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c235 := h 234 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c1418 := derived1418 a h
  have h5 : Entails.eval a c1427 := derived1427 a h
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1603 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1601, some c631, some c1460, some c36, some c23, some c813, some c1602, some c358, some c354, some c37, some c210, some c58, some c50, some c64, some c320, some c250, some c351, some c315, some c276, some c94, some c311, some c316, some c382, some c309, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1603 : lratChecker f1603 p1603 = .success := by decide +kernel
theorem unsat1603 : Unsatisfiable (PosFin 57) f1603 := by
  apply lratCheckerSound f1603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1603
  · intro a ha; simp [p1603] at ha; subst a; trivial
  · exact checked1603
theorem derived1603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1603 := by
  apply localUnsat_implies_entails f1603 [c1569, c1601, c631, c1460, c36, c23, c813, c1602, c358, c354, c37, c210, c58, c50, c64, c320, c250, c351, c315, c276, c94, c311, c316, c382, c309] c1603 unsat1603 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1460 := derived1460 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c813 := derived813 a h
  have h7 : Entails.eval a c1602 := derived1602 a h
  have h8 : Entails.eval a c358 := h 357 (by decide)
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c64 := h 63 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c250 := h 249 (by decide)
  have h17 : Entails.eval a c351 := h 350 (by decide)
  have h18 : Entails.eval a c315 := h 314 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  have h20 : Entails.eval a c94 := h 93 (by decide)
  have h21 : Entails.eval a c311 := h 310 (by decide)
  have h22 : Entails.eval a c316 := h 315 (by decide)
  have h23 : Entails.eval a c382 := h 381 (by decide)
  have h24 : Entails.eval a c309 := h 308 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1604 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1601, some c24, some c120, some c16, some c127, some c119, some c331, some c92, some c813, some c243, some c235, some c271, some c233, some c136, some c245, some c356, some c1139, some c333, some c174, some c178, some c323, some c205, some c161, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1604 : lratChecker f1604 p1604 = .success := by decide +kernel
theorem unsat1604 : Unsatisfiable (PosFin 57) f1604 := by
  apply lratCheckerSound f1604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1604
  · intro a ha; simp [p1604] at ha; subst a; trivial
  · exact checked1604
theorem derived1604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1604 := by
  apply localUnsat_implies_entails f1604 [c1569, c1601, c24, c120, c16, c127, c119, c331, c92, c813, c243, c235, c271, c233, c136, c245, c356, c1139, c333, c174, c178, c323, c205, c161] c1604 unsat1604 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c243 := h 242 (by decide)
  have h11 : Entails.eval a c235 := h 234 (by decide)
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c233 := h 232 (by decide)
  have h14 : Entails.eval a c136 := h 135 (by decide)
  have h15 : Entails.eval a c245 := h 244 (by decide)
  have h16 : Entails.eval a c356 := h 355 (by decide)
  have h17 : Entails.eval a c1139 := derived1139 a h
  have h18 : Entails.eval a c333 := h 332 (by decide)
  have h19 : Entails.eval a c174 := h 173 (by decide)
  have h20 : Entails.eval a c178 := h 177 (by decide)
  have h21 : Entails.eval a c323 := h 322 (by decide)
  have h22 : Entails.eval a c205 := h 204 (by decide)
  have h23 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1605 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨37, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1049, some c8, some c128, some c92, some c127, some c1580, some c14, some c1034, some c145, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1605 : lratChecker f1605 p1605 = .success := by decide +kernel
theorem unsat1605 : Unsatisfiable (PosFin 57) f1605 := by
  apply lratCheckerSound f1605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1605
  · intro a ha; simp [p1605] at ha; subst a; trivial
  · exact checked1605
theorem derived1605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1605 := by
  apply localUnsat_implies_entails f1605 [c1569, c1049, c8, c128, c92, c127, c1580, c14, c1034, c145] c1605 unsat1605 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c128 := h 127 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c1580 := derived1580 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c1034 := derived1034 a h
  have h9 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1606 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1601, some c1603, some c1604, some c358, some c354, some c1590, some c161, some c1573, some c1049, some c1605, some c31, some c1138, some c33, some c6, some c163, some c136, some c137, some c124, some c14, some c206, some c333, some c88, some c182, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1606 : lratChecker f1606 p1606 = .success := by decide +kernel
theorem unsat1606 : Unsatisfiable (PosFin 57) f1606 := by
  apply lratCheckerSound f1606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1606
  · intro a ha; simp [p1606] at ha; subst a; trivial
  · exact checked1606
theorem derived1606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1606 := by
  apply localUnsat_implies_entails f1606 [c1569, c1601, c1603, c1604, c358, c354, c1590, c161, c1573, c1049, c1605, c31, c1138, c33, c6, c163, c136, c137, c124, c14, c206, c333, c88, c182] c1606 unsat1606 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1603 := derived1603 a h
  have h3 : Entails.eval a c1604 := derived1604 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c1590 := derived1590 a h
  have h7 : Entails.eval a c161 := h 160 (by decide)
  have h8 : Entails.eval a c1573 := derived1573 a h
  have h9 : Entails.eval a c1049 := derived1049 a h
  have h10 : Entails.eval a c1605 := derived1605 a h
  have h11 : Entails.eval a c31 := h 30 (by decide)
  have h12 : Entails.eval a c1138 := derived1138 a h
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c6 := h 5 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c137 := h 136 (by decide)
  have h18 : Entails.eval a c124 := h 123 (by decide)
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c333 := h 332 (by decide)
  have h22 : Entails.eval a c88 := h 87 (by decide)
  have h23 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1607 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1606, some c22, some c1460, some c1415, some c76, some c1602, some c813, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1607 : lratChecker f1607 p1607 = .success := by decide +kernel
theorem unsat1607 : Unsatisfiable (PosFin 57) f1607 := by
  apply lratCheckerSound f1607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1607
  · intro a ha; simp [p1607] at ha; subst a; trivial
  · exact checked1607
theorem derived1607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1607 := by
  apply localUnsat_implies_entails f1607 [c1569, c1606, c22, c1460, c1415, c76, c1602, c813] c1607 unsat1607 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1606 := derived1606 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c1460 := derived1460 a h
  have h4 : Entails.eval a c1415 := derived1415 a h
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c1602 := derived1602 a h
  have h7 : Entails.eval a c813 := derived813 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1608 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1607, some c1606, some c631, some c22, some c42, some c210, some c141, some c45, some c250, some c1584, some c1601, some c24, some c120, some c16, some c127, some c119, some c331, some c92, some c90, some c323, some c813, some c243, some c247, some c174, some c271, some c233, some c136, some c356, some c1139, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1608 : lratChecker f1608 p1608 = .success := by decide +kernel
theorem unsat1608 : Unsatisfiable (PosFin 57) f1608 := by
  apply lratCheckerSound f1608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1608
  · intro a ha; simp [p1608] at ha; subst a; trivial
  · exact checked1608
theorem derived1608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1608 := by
  apply localUnsat_implies_entails f1608 [c1569, c1607, c1606, c631, c22, c42, c210, c141, c45, c250, c1584, c1601, c24, c120, c16, c127, c119, c331, c92, c90, c323, c813, c243, c247, c174, c271, c233, c136, c356, c1139] c1608 unsat1608 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1607 := derived1607 a h
  have h2 : Entails.eval a c1606 := derived1606 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c1584 := derived1584 a h
  have h11 : Entails.eval a c1601 := derived1601 a h
  have h12 : Entails.eval a c24 := h 23 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c127 := h 126 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c331 := h 330 (by decide)
  have h18 : Entails.eval a c92 := h 91 (by decide)
  have h19 : Entails.eval a c90 := h 89 (by decide)
  have h20 : Entails.eval a c323 := h 322 (by decide)
  have h21 : Entails.eval a c813 := derived813 a h
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c247 := h 246 (by decide)
  have h24 : Entails.eval a c174 := h 173 (by decide)
  have h25 : Entails.eval a c271 := h 270 (by decide)
  have h26 : Entails.eval a c233 := h 232 (by decide)
  have h27 : Entails.eval a c136 := h 135 (by decide)
  have h28 : Entails.eval a c356 := h 355 (by decide)
  have h29 : Entails.eval a c1139 := derived1139 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1609 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨39, by decide⟩, true), (⟨33, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨23, by decide⟩, true), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c356, some c1160, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1609 : lratChecker f1609 p1609 = .success := by decide +kernel
theorem unsat1609 : Unsatisfiable (PosFin 57) f1609 := by
  apply lratCheckerSound f1609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1609
  · intro a ha; simp [p1609] at ha; subst a; trivial
  · exact checked1609
theorem derived1609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1609 := by
  apply localUnsat_implies_entails f1609 [c1147, c356, c1160] c1609 unsat1609 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c1160 := derived1160 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1610 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1601, some c631, some c1606, some c22, some c42, some c210, some c141, some c45, some c54, some c250, some c1584, some c98, some c1607, some c1608, some c355, some c340, some c119, some c1579, some c14, some c1609, some c229, some c356, some c232, some c712, some c658, some c320, some c55, some c151, some c145, some c6, some c337, some c149, some c311, some c318, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1610 : lratChecker f1610 p1610 = .success := by decide +kernel
theorem unsat1610 : Unsatisfiable (PosFin 57) f1610 := by
  apply lratCheckerSound f1610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1610
  · intro a ha; simp [p1610] at ha; subst a; trivial
  · exact checked1610
theorem derived1610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1610 := by
  apply localUnsat_implies_entails f1610 [c1569, c1601, c631, c1606, c22, c42, c210, c141, c45, c54, c250, c1584, c98, c1607, c1608, c355, c340, c119, c1579, c14, c1609, c229, c356, c232, c712, c658, c320, c55, c151, c145, c6, c337, c149, c311, c318] c1610 unsat1610 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1606 := derived1606 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c250 := h 249 (by decide)
  have h11 : Entails.eval a c1584 := derived1584 a h
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c1607 := derived1607 a h
  have h14 : Entails.eval a c1608 := derived1608 a h
  have h15 : Entails.eval a c355 := h 354 (by decide)
  have h16 : Entails.eval a c340 := h 339 (by decide)
  have h17 : Entails.eval a c119 := h 118 (by decide)
  have h18 : Entails.eval a c1579 := derived1579 a h
  have h19 : Entails.eval a c14 := h 13 (by decide)
  have h20 : Entails.eval a c1609 := derived1609 a h
  have h21 : Entails.eval a c229 := h 228 (by decide)
  have h22 : Entails.eval a c356 := h 355 (by decide)
  have h23 : Entails.eval a c232 := h 231 (by decide)
  have h24 : Entails.eval a c712 := derived712 a h
  have h25 : Entails.eval a c658 := derived658 a h
  have h26 : Entails.eval a c320 := h 319 (by decide)
  have h27 : Entails.eval a c55 := h 54 (by decide)
  have h28 : Entails.eval a c151 := h 150 (by decide)
  have h29 : Entails.eval a c145 := h 144 (by decide)
  have h30 : Entails.eval a c6 := h 5 (by decide)
  have h31 : Entails.eval a c337 := h 336 (by decide)
  have h32 : Entails.eval a c149 := h 148 (by decide)
  have h33 : Entails.eval a c311 := h 310 (by decide)
  have h34 : Entails.eval a c318 := h 317 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1611 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1610, some c24, some c120, some c15, some c1601, some c23, some c813, some c235, some c1282, some c29, some c631, some c356, some c1454, some c233, some c269, some c140, some c126, some c134, some c541, some c327, some c208, some c173, some c145, some c1302, some c204, some c209, some c151, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1611 : lratChecker f1611 p1611 = .success := by decide +kernel
theorem unsat1611 : Unsatisfiable (PosFin 57) f1611 := by
  apply lratCheckerSound f1611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1611
  · intro a ha; simp [p1611] at ha; subst a; trivial
  · exact checked1611
theorem derived1611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1611 := by
  apply localUnsat_implies_entails f1611 [c1569, c1610, c24, c120, c15, c1601, c23, c813, c235, c1282, c29, c631, c356, c1454, c233, c269, c140, c126, c134, c541, c327, c208, c173, c145, c1302, c204, c209, c151] c1611 unsat1611 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1610 := derived1610 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1601 := derived1601 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c235 := h 234 (by decide)
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c631 := derived631 a h
  have h12 : Entails.eval a c356 := h 355 (by decide)
  have h13 : Entails.eval a c1454 := derived1454 a h
  have h14 : Entails.eval a c233 := h 232 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c140 := h 139 (by decide)
  have h17 : Entails.eval a c126 := h 125 (by decide)
  have h18 : Entails.eval a c134 := h 133 (by decide)
  have h19 : Entails.eval a c541 := derived541 a h
  have h20 : Entails.eval a c327 := h 326 (by decide)
  have h21 : Entails.eval a c208 := h 207 (by decide)
  have h22 : Entails.eval a c173 := h 172 (by decide)
  have h23 : Entails.eval a c145 := h 144 (by decide)
  have h24 : Entails.eval a c1302 := derived1302 a h
  have h25 : Entails.eval a c204 := h 203 (by decide)
  have h26 : Entails.eval a c209 := h 208 (by decide)
  have h27 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1612 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨26, by decide⟩, false), (⟨34, by decide⟩, true), (⟨14, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨18, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c1138, some c269, some c214, some c134, some c144, some c1139, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1612 : lratChecker f1612 p1612 = .success := by decide +kernel
theorem unsat1612 : Unsatisfiable (PosFin 57) f1612 := by
  apply lratCheckerSound f1612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1612
  · intro a ha; simp [p1612] at ha; subst a; trivial
  · exact checked1612
theorem derived1612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1612 := by
  apply localUnsat_implies_entails f1612 [c233, c1138, c269, c214, c134, c144, c1139] c1612 unsat1612 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c1138 := derived1138 a h
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c214 := h 213 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c1139 := derived1139 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1613 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, true), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨21, by decide⟩, false), (⟨39, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c45, some c54, some c338, some c339, some c249, some c312, some c310, some c320, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1613 : lratChecker f1613 p1613 = .success := by decide +kernel
theorem unsat1613 : Unsatisfiable (PosFin 57) f1613 := by
  apply lratCheckerSound f1613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1613
  · intro a ha; simp [p1613] at ha; subst a; trivial
  · exact checked1613
theorem derived1613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1613 := by
  apply localUnsat_implies_entails f1613 [c1569, c45, c54, c338, c339, c249, c312, c310, c320] c1613 unsat1613 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c339 := h 338 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c312 := h 311 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1614 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨36, by decide⟩, false), (⟨34, by decide⟩, true), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨21, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, true), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c23, some c813, some c1282, some c68, some c29, some c269, some c773, some c32, some c1613, some c209, some c145, some c12, some c136, some c124, some c208, some c89, some c329, some c178, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1614 : lratChecker f1614 p1614 = .success := by decide +kernel
theorem unsat1614 : Unsatisfiable (PosFin 57) f1614 := by
  apply lratCheckerSound f1614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1614
  · intro a ha; simp [p1614] at ha; subst a; trivial
  · exact checked1614
theorem derived1614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1614 := by
  apply localUnsat_implies_entails f1614 [c1569, c23, c813, c1282, c68, c29, c269, c773, c32, c1613, c209, c145, c12, c136, c124, c208, c89, c329, c178] c1614 unsat1614 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c773 := derived773 a h
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c1613 := derived1613 a h
  have h10 : Entails.eval a c209 := h 208 (by decide)
  have h11 : Entails.eval a c145 := h 144 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c208 := h 207 (by decide)
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1615 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1610, some c24, some c120, some c15, some c1601, some c23, some c813, some c235, some c1282, some c29, some c631, some c1611, some c38, some c1612, some c1614, some c126, some c541, some c91, some c333, some c175, some c245, some c1139, some c1243, some c134, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1615 : lratChecker f1615 p1615 = .success := by decide +kernel
theorem unsat1615 : Unsatisfiable (PosFin 57) f1615 := by
  apply lratCheckerSound f1615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1615
  · intro a ha; simp [p1615] at ha; subst a; trivial
  · exact checked1615
theorem derived1615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1615 := by
  apply localUnsat_implies_entails f1615 [c1569, c1610, c24, c120, c15, c1601, c23, c813, c235, c1282, c29, c631, c1611, c38, c1612, c1614, c126, c541, c91, c333, c175, c245, c1139, c1243, c134] c1615 unsat1615 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1610 := derived1610 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1601 := derived1601 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c235 := h 234 (by decide)
  have h9 : Entails.eval a c1282 := derived1282 a h
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c631 := derived631 a h
  have h12 : Entails.eval a c1611 := derived1611 a h
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c1612 := derived1612 a h
  have h15 : Entails.eval a c1614 := derived1614 a h
  have h16 : Entails.eval a c126 := h 125 (by decide)
  have h17 : Entails.eval a c541 := derived541 a h
  have h18 : Entails.eval a c91 := h 90 (by decide)
  have h19 : Entails.eval a c333 := h 332 (by decide)
  have h20 : Entails.eval a c175 := h 174 (by decide)
  have h21 : Entails.eval a c245 := h 244 (by decide)
  have h22 : Entails.eval a c1139 := derived1139 a h
  have h23 : Entails.eval a c1243 := derived1243 a h
  have h24 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1616 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨21, by decide⟩, false), (⟨37, by decide⟩, true), (⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c65, some c1049, some c1034, some c356, some c145, some c67, some c163, some c12, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1616 : lratChecker f1616 p1616 = .success := by decide +kernel
theorem unsat1616 : Unsatisfiable (PosFin 57) f1616 := by
  apply lratCheckerSound f1616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1616
  · intro a ha; simp [p1616] at ha; subst a; trivial
  · exact checked1616
theorem derived1616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1616 := by
  apply localUnsat_implies_entails f1616 [c1569, c65, c1049, c1034, c356, c145, c67, c163, c12] c1616 unsat1616 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c1034 := derived1034 a h
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1617 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1601, some c23, some c813, some c1610, some c1282, some c29, some c631, some c24, some c120, some c235, some c15, some c1616, some c1615, some c118, some c146, some c210, some c215, some c53, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1617 : lratChecker f1617 p1617 = .success := by decide +kernel
theorem unsat1617 : Unsatisfiable (PosFin 57) f1617 := by
  apply lratCheckerSound f1617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1617
  · intro a ha; simp [p1617] at ha; subst a; trivial
  · exact checked1617
theorem derived1617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1617 := by
  apply localUnsat_implies_entails f1617 [c1569, c1601, c23, c813, c1610, c1282, c29, c631, c24, c120, c235, c15, c1616, c1615, c118, c146, c210, c215, c53] c1617 unsat1617 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c813 := derived813 a h
  have h4 : Entails.eval a c1610 := derived1610 a h
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c1616 := derived1616 a h
  have h13 : Entails.eval a c1615 := derived1615 a h
  have h14 : Entails.eval a c118 := h 117 (by decide)
  have h15 : Entails.eval a c146 := h 145 (by decide)
  have h16 : Entails.eval a c210 := h 209 (by decide)
  have h17 : Entails.eval a c215 := h 214 (by decide)
  have h18 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1618 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1610, some c1282, some c1601, some c23, some c1617, some c1590, some c355, some c1595, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1618 : lratChecker f1618 p1618 = .success := by decide +kernel
theorem unsat1618 : Unsatisfiable (PosFin 57) f1618 := by
  apply lratCheckerSound f1618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1618
  · intro a ha; simp [p1618] at ha; subst a; trivial
  · exact checked1618
theorem derived1618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1618 := by
  apply localUnsat_implies_entails f1618 [c1610, c1282, c1601, c23, c1617, c1590, c355, c1595] c1618 unsat1618 (by rfl) a
  have h0 : Entails.eval a c1610 := derived1610 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c1617 := derived1617 a h
  have h5 : Entails.eval a c1590 := derived1590 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c1595 := derived1595 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1619 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1618, some c1610, some c1282, some c1601, some c24, some c120, some c1604, some c15, some c16, some c1595, some c118, some c146, some c172, some c127, some c773, some c331, some c92, some c323, some c356, some c174, some c243, some c233, some c793, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1619 : lratChecker f1619 p1619 = .success := by decide +kernel
theorem unsat1619 : Unsatisfiable (PosFin 57) f1619 := by
  apply lratCheckerSound f1619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1619
  · intro a ha; simp [p1619] at ha; subst a; trivial
  · exact checked1619
theorem derived1619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1619 := by
  apply localUnsat_implies_entails f1619 [c1618, c1610, c1282, c1601, c24, c120, c1604, c15, c16, c1595, c118, c146, c172, c127, c773, c331, c92, c323, c356, c174, c243, c233, c793] c1619 unsat1619 (by rfl) a
  have h0 : Entails.eval a c1618 := derived1618 a h
  have h1 : Entails.eval a c1610 := derived1610 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1601 := derived1601 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c1604 := derived1604 a h
  have h7 : Entails.eval a c15 := h 14 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c1595 := derived1595 a h
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c172 := h 171 (by decide)
  have h13 : Entails.eval a c127 := h 126 (by decide)
  have h14 : Entails.eval a c773 := derived773 a h
  have h15 : Entails.eval a c331 := h 330 (by decide)
  have h16 : Entails.eval a c92 := h 91 (by decide)
  have h17 : Entails.eval a c323 := h 322 (by decide)
  have h18 : Entails.eval a c356 := h 355 (by decide)
  have h19 : Entails.eval a c174 := h 173 (by decide)
  have h20 : Entails.eval a c243 := h 242 (by decide)
  have h21 : Entails.eval a c233 := h 232 (by decide)
  have h22 : Entails.eval a c793 := derived793 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1620 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨18, by decide⟩, true), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c16, some c128, some c92, some c418, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p1620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1620 : lratChecker f1620 p1620 = .success := by decide +kernel
theorem unsat1620 : Unsatisfiable (PosFin 57) f1620 := by
  apply lratCheckerSound f1620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1620
  · intro a ha; simp [p1620] at ha; subst a; trivial
  · exact checked1620
theorem derived1620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1620 := by
  apply localUnsat_implies_entails f1620 [c119, c16, c128, c92, c418] c1620 unsat1620 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c418 := derived418 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1621 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1601, some c1610, some c1282, some c1619, some c1590, some c1595, some c355, some c236, some c119, some c1618, some c232, some c269, some c1620, some c31, some c525, some c793, some c28, some c14, some c117, some c125, some c532, some c330, some c174, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1621 : lratChecker f1621 p1621 = .success := by decide +kernel
theorem unsat1621 : Unsatisfiable (PosFin 57) f1621 := by
  apply lratCheckerSound f1621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1621
  · intro a ha; simp [p1621] at ha; subst a; trivial
  · exact checked1621
theorem derived1621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1621 := by
  apply localUnsat_implies_entails f1621 [c1601, c1610, c1282, c1619, c1590, c1595, c355, c236, c119, c1618, c232, c269, c1620, c31, c525, c793, c28, c14, c117, c125, c532, c330, c174] c1621 unsat1621 (by rfl) a
  have h0 : Entails.eval a c1601 := derived1601 a h
  have h1 : Entails.eval a c1610 := derived1610 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1619 := derived1619 a h
  have h4 : Entails.eval a c1590 := derived1590 a h
  have h5 : Entails.eval a c1595 := derived1595 a h
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c1618 := derived1618 a h
  have h10 : Entails.eval a c232 := h 231 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c1620 := derived1620 a h
  have h13 : Entails.eval a c31 := h 30 (by decide)
  have h14 : Entails.eval a c525 := derived525 a h
  have h15 : Entails.eval a c793 := derived793 a h
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c117 := h 116 (by decide)
  have h19 : Entails.eval a c125 := h 124 (by decide)
  have h20 : Entails.eval a c532 := derived532 a h
  have h21 : Entails.eval a c330 := h 329 (by decide)
  have h22 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1622 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1601, some c1610, some c1282, some c1619, some c1590, some c1595, some c355, some c236, some c1621, some c359, some c356, some c229, some c773, some c691, some c282, some c313, some c320, some c54, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1622 : lratChecker f1622 p1622 = .success := by decide +kernel
theorem unsat1622 : Unsatisfiable (PosFin 57) f1622 := by
  apply lratCheckerSound f1622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1622
  · intro a ha; simp [p1622] at ha; subst a; trivial
  · exact checked1622
theorem derived1622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1622 := by
  apply localUnsat_implies_entails f1622 [c1569, c1601, c1610, c1282, c1619, c1590, c1595, c355, c236, c1621, c359, c356, c229, c773, c691, c282, c313, c320, c54] c1622 unsat1622 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1601 := derived1601 a h
  have h2 : Entails.eval a c1610 := derived1610 a h
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c1619 := derived1619 a h
  have h5 : Entails.eval a c1590 := derived1590 a h
  have h6 : Entails.eval a c1595 := derived1595 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c236 := h 235 (by decide)
  have h9 : Entails.eval a c1621 := derived1621 a h
  have h10 : Entails.eval a c359 := h 358 (by decide)
  have h11 : Entails.eval a c356 := h 355 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c773 := derived773 a h
  have h14 : Entails.eval a c691 := derived691 a h
  have h15 : Entails.eval a c282 := h 281 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c320 := h 319 (by decide)
  have h18 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1623 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1601, some c23, some c360, some c1622, some c631, some c1462, some c36, some c1602, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1623 : lratChecker f1623 p1623 = .success := by decide +kernel
theorem unsat1623 : Unsatisfiable (PosFin 57) f1623 := by
  apply lratCheckerSound f1623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1623
  · intro a ha; simp [p1623] at ha; subst a; trivial
  · exact checked1623
theorem derived1623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1623 := by
  apply localUnsat_implies_entails f1623 [c1601, c23, c360, c1622, c631, c1462, c36, c1602] c1623 unsat1623 (by rfl) a
  have h0 : Entails.eval a c1601 := derived1601 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c1622 := derived1622 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1462 := derived1462 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c1602 := derived1602 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1624 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1622, some c1077, some c356, some c233, some c120, some c24, some c1601, some c631, some c23, some c360, some c235, some c271, some c1623, some c1282, some c15, some c1461, some c269, some c140, some c134, some c208, some c1014, some c1302, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1624 : lratChecker f1624 p1624 = .success := by decide +kernel
theorem unsat1624 : Unsatisfiable (PosFin 57) f1624 := by
  apply lratCheckerSound f1624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1624
  · intro a ha; simp [p1624] at ha; subst a; trivial
  · exact checked1624
theorem derived1624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1624 := by
  apply localUnsat_implies_entails f1624 [c1622, c1077, c356, c233, c120, c24, c1601, c631, c23, c360, c235, c271, c1623, c1282, c15, c1461, c269, c140, c134, c208, c1014, c1302] c1624 unsat1624 (by rfl) a
  have h0 : Entails.eval a c1622 := derived1622 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c233 := h 232 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c1601 := derived1601 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c1623 := derived1623 a h
  have h13 : Entails.eval a c1282 := derived1282 a h
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c1461 := derived1461 a h
  have h16 : Entails.eval a c269 := h 268 (by decide)
  have h17 : Entails.eval a c140 := h 139 (by decide)
  have h18 : Entails.eval a c134 := h 133 (by decide)
  have h19 : Entails.eval a c208 := h 207 (by decide)
  have h20 : Entails.eval a c1014 := derived1014 a h
  have h21 : Entails.eval a c1302 := derived1302 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1625 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1622, some c1077, some c356, some c1601, some c24, some c120, some c233, some c1624, some c16, some c127, some c119, some c87, some c92, some c360, some c243, some c235, some c271, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1625 : lratChecker f1625 p1625 = .success := by decide +kernel
theorem unsat1625 : Unsatisfiable (PosFin 57) f1625 := by
  apply lratCheckerSound f1625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1625
  · intro a ha; simp [p1625] at ha; subst a; trivial
  · exact checked1625
theorem derived1625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1625 := by
  apply localUnsat_implies_entails f1625 [c1622, c1077, c356, c1601, c24, c120, c233, c1624, c16, c127, c119, c87, c92, c360, c243, c235, c271] c1625 unsat1625 (by rfl) a
  have h0 : Entails.eval a c1622 := derived1622 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c1601 := derived1601 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c233 := h 232 (by decide)
  have h7 : Entails.eval a c1624 := derived1624 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c119 := h 118 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c360 := h 359 (by decide)
  have h14 : Entails.eval a c243 := h 242 (by decide)
  have h15 : Entails.eval a c235 := h 234 (by decide)
  have h16 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1626 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1622, some c1077, some c1625, some c358, some c1601, some c23, some c1463, some c355, some c1595, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1626 : lratChecker f1626 p1626 = .success := by decide +kernel
theorem unsat1626 : Unsatisfiable (PosFin 57) f1626 := by
  apply lratCheckerSound f1626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1626
  · intro a ha; simp [p1626] at ha; subst a; trivial
  · exact checked1626
theorem derived1626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1626 := by
  apply localUnsat_implies_entails f1626 [c1622, c1077, c1625, c358, c1601, c23, c1463, c355, c1595] c1626 unsat1626 (by rfl) a
  have h0 : Entails.eval a c1622 := derived1622 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1625 := derived1625 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c1601 := derived1601 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c1463 := derived1463 a h
  have h7 : Entails.eval a c355 := h 354 (by decide)
  have h8 : Entails.eval a c1595 := derived1595 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1627 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1626, some c1622, some c1077, some c1625, some c358, some c356, some c1601, some c631, some c1539, some c1447, some c232, some c1494, some c268, some c1620, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1627 : lratChecker f1627 p1627 = .success := by decide +kernel
theorem unsat1627 : Unsatisfiable (PosFin 57) f1627 := by
  apply lratCheckerSound f1627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1627
  · intro a ha; simp [p1627] at ha; subst a; trivial
  · exact checked1627
theorem derived1627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1627 := by
  apply localUnsat_implies_entails f1627 [c1626, c1622, c1077, c1625, c358, c356, c1601, c631, c1539, c1447, c232, c1494, c268, c1620] c1627 unsat1627 (by rfl) a
  have h0 : Entails.eval a c1626 := derived1626 a h
  have h1 : Entails.eval a c1622 := derived1622 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1625 := derived1625 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c1601 := derived1601 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c1539 := derived1539 a h
  have h9 : Entails.eval a c1447 := derived1447 a h
  have h10 : Entails.eval a c232 := h 231 (by decide)
  have h11 : Entails.eval a c1494 := derived1494 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c1620 := derived1620 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1628 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1601, some c1622, some c1077, some c356, some c1625, some c358, some c1626, some c1627, some c1282, some c1595, some c1495, some c355, some c1620, some c236, some c232, some c269, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1628 : lratChecker f1628 p1628 = .success := by decide +kernel
theorem unsat1628 : Unsatisfiable (PosFin 57) f1628 := by
  apply lratCheckerSound f1628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1628
  · intro a ha; simp [p1628] at ha; subst a; trivial
  · exact checked1628
theorem derived1628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1628 := by
  apply localUnsat_implies_entails f1628 [c1601, c1622, c1077, c356, c1625, c358, c1626, c1627, c1282, c1595, c1495, c355, c1620, c236, c232, c269] c1628 unsat1628 (by rfl) a
  have h0 : Entails.eval a c1601 := derived1601 a h
  have h1 : Entails.eval a c1622 := derived1622 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c1625 := derived1625 a h
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c1626 := derived1626 a h
  have h7 : Entails.eval a c1627 := derived1627 a h
  have h8 : Entails.eval a c1282 := derived1282 a h
  have h9 : Entails.eval a c1595 := derived1595 a h
  have h10 : Entails.eval a c1495 := derived1495 a h
  have h11 : Entails.eval a c355 := h 354 (by decide)
  have h12 : Entails.eval a c1620 := derived1620 a h
  have h13 : Entails.eval a c236 := h 235 (by decide)
  have h14 : Entails.eval a c232 := h 231 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1629 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨36, by decide⟩, true), (⟨8, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c15, some c169, some c148, some c205, some c216, some c1230, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1629 : lratChecker f1629 p1629 = .success := by decide +kernel
theorem unsat1629 : Unsatisfiable (PosFin 57) f1629 := by
  apply lratCheckerSound f1629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1629
  · intro a ha; simp [p1629] at ha; subst a; trivial
  · exact checked1629
theorem derived1629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1629 := by
  apply localUnsat_implies_entails f1629 [c15, c169, c148, c205, c216, c1230] c1629 unsat1629 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c205 := h 204 (by decide)
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c1230 := derived1230 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1630 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true), (⟨36, by decide⟩, true), (⟨18, by decide⟩, false), (⟨37, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c134, some c208, some c204, some c1302, some c144, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1630 : lratChecker f1630 p1630 = .success := by decide +kernel
theorem unsat1630 : Unsatisfiable (PosFin 57) f1630 := by
  apply lratCheckerSound f1630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1630
  · intro a ha; simp [p1630] at ha; subst a; trivial
  · exact checked1630
theorem derived1630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1630 := by
  apply localUnsat_implies_entails f1630 [c268, c134, c208, c204, c1302, c144] c1630 unsat1630 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c1302 := derived1302 a h
  have h5 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1631 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨41, by decide⟩, true), (⟨14, by decide⟩, true), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨7, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c266, some c126, some c1436, some c267, some c1303, some c1282, some c29, some c23, some c1630, some c32, some c116, some c89, some c204, some c244, some c174, some c331, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1631 : lratChecker f1631 p1631 = .success := by decide +kernel
theorem unsat1631 : Unsatisfiable (PosFin 57) f1631 := by
  apply lratCheckerSound f1631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1631
  · intro a ha; simp [p1631] at ha; subst a; trivial
  · exact checked1631
theorem derived1631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1631 := by
  apply localUnsat_implies_entails f1631 [c631, c1628, c266, c126, c1436, c267, c1303, c1282, c29, c23, c1630, c32, c116, c89, c204, c244, c174, c331] c1631 unsat1631 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c126 := h 125 (by decide)
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c1303 := derived1303 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c1630 := derived1630 a h
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c244 := h 243 (by decide)
  have h16 : Entails.eval a c174 := h 173 (by decide)
  have h17 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1632 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨8, by decide⟩, false), (⟨37, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c267, some c1303, some c1282, some c29, some c266, some c1629, some c126, some c541, some c1631, some c173, some c327, some c38, some c68, some c164, some c216, some c1414, some c281, some c666, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1632 : lratChecker f1632 p1632 = .success := by decide +kernel
theorem unsat1632 : Unsatisfiable (PosFin 57) f1632 := by
  apply lratCheckerSound f1632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1632
  · intro a ha; simp [p1632] at ha; subst a; trivial
  · exact checked1632
theorem derived1632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1632 := by
  apply localUnsat_implies_entails f1632 [c631, c1628, c267, c1303, c1282, c29, c266, c1629, c126, c541, c1631, c173, c327, c38, c68, c164, c216, c1414, c281, c666] c1632 unsat1632 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c1303 := derived1303 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c1629 := derived1629 a h
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c541 := derived541 a h
  have h10 : Entails.eval a c1631 := derived1631 a h
  have h11 : Entails.eval a c173 := h 172 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c164 := h 163 (by decide)
  have h16 : Entails.eval a c216 := h 215 (by decide)
  have h17 : Entails.eval a c1414 := derived1414 a h
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c666 := derived666 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1633 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨8, by decide⟩, false), (⟨37, by decide⟩, true), (⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c267, some c1303, some c1282, some c29, some c23, some c266, some c1632, some c356, some c38, some c216, some c148, some c15, some c126, some c541, some c333, some c175, some c1139, some c134, some c174, some c268, some c331, some c244, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1633 : lratChecker f1633 p1633 = .success := by decide +kernel
theorem unsat1633 : Unsatisfiable (PosFin 57) f1633 := by
  apply lratCheckerSound f1633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1633
  · intro a ha; simp [p1633] at ha; subst a; trivial
  · exact checked1633
theorem derived1633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1633 := by
  apply localUnsat_implies_entails f1633 [c631, c1628, c267, c1303, c1282, c29, c23, c266, c1632, c356, c38, c216, c148, c15, c126, c541, c333, c175, c1139, c134, c174, c268, c331, c244] c1633 unsat1633 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c1303 := derived1303 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1632 := derived1632 a h
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c148 := h 147 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c541 := derived541 a h
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c175 := h 174 (by decide)
  have h18 : Entails.eval a c1139 := derived1139 a h
  have h19 : Entails.eval a c134 := h 133 (by decide)
  have h20 : Entails.eval a c174 := h 173 (by decide)
  have h21 : Entails.eval a c268 := h 267 (by decide)
  have h22 : Entails.eval a c331 := h 330 (by decide)
  have h23 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1634 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨2, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c65, some c1049, some c1616, some c356, some c117, some c67, some c163, some c12, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1634 : lratChecker f1634 p1634 = .success := by decide +kernel
theorem unsat1634 : Unsatisfiable (PosFin 57) f1634 := by
  apply lratCheckerSound f1634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1634
  · intro a ha; simp [p1634] at ha; subst a; trivial
  · exact checked1634
theorem derived1634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1634 := by
  apply localUnsat_implies_entails f1634 [c1569, c65, c1049, c1616, c356, c117, c67, c163, c12] c1634 unsat1634 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c65 := h 64 (by decide)
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c1616 := derived1616 a h
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1635 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1628, some c266, some c267, some c1303, some c23, some c1282, some c813, some c29, some c1466, some c1634, some c1633, some c118, some c15, some c1629, some c148, some c356, some c216, some c38, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1635 : lratChecker f1635 p1635 = .success := by decide +kernel
theorem unsat1635 : Unsatisfiable (PosFin 57) f1635 := by
  apply lratCheckerSound f1635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1635
  · intro a ha; simp [p1635] at ha; subst a; trivial
  · exact checked1635
theorem derived1635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1635 := by
  apply localUnsat_implies_entails f1635 [c1569, c631, c1628, c266, c267, c1303, c23, c1282, c813, c29, c1466, c1634, c1633, c118, c15, c1629, c148, c356, c216, c38] c1635 unsat1635 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c1303 := derived1303 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c1466 := derived1466 a h
  have h11 : Entails.eval a c1634 := derived1634 a h
  have h12 : Entails.eval a c1633 := derived1633 a h
  have h13 : Entails.eval a c118 := h 117 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c1629 := derived1629 a h
  have h16 : Entails.eval a c148 := h 147 (by decide)
  have h17 : Entails.eval a c356 := h 355 (by decide)
  have h18 : Entails.eval a c216 := h 215 (by decide)
  have h19 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1636 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c232, some c525, some c34, some c14, some c138, some c638, some c206, some c205, some c169, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1636 : lratChecker f1636 p1636 = .success := by decide +kernel
theorem unsat1636 : Unsatisfiable (PosFin 57) f1636 := by
  apply lratCheckerSound f1636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1636
  · intro a ha; simp [p1636] at ha; subst a; trivial
  · exact checked1636
theorem derived1636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1636 := by
  apply localUnsat_implies_entails f1636 [c119, c232, c525, c34, c14, c138, c638, c206, c205, c169] c1636 unsat1636 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c232 := h 231 (by decide)
  have h2 : Entails.eval a c525 := derived525 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c638 := derived638 a h
  have h7 : Entails.eval a c206 := h 205 (by decide)
  have h8 : Entails.eval a c205 := h 204 (by decide)
  have h9 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1637 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c1636, some c356, some c229, some c38, some c1156, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1637 : lratChecker f1637 p1637 = .success := by decide +kernel
theorem unsat1637 : Unsatisfiable (PosFin 57) f1637 := by
  apply lratCheckerSound f1637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1637
  · intro a ha; simp [p1637] at ha; subst a; trivial
  · exact checked1637
theorem derived1637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1637 := by
  apply localUnsat_implies_entails f1637 [c119, c1636, c356, c229, c38, c1156] c1637 unsat1637 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c1636 := derived1636 a h
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c1156 := derived1156 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1638 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨18, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c1436, some c133, some c206, some c205, some c169, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1638 : lratChecker f1638 p1638 = .success := by decide +kernel
theorem unsat1638 : Unsatisfiable (PosFin 57) f1638 := by
  apply lratCheckerSound f1638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1638
  · intro a ha; simp [p1638] at ha; subst a; trivial
  · exact checked1638
theorem derived1638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1638 := by
  apply localUnsat_implies_entails f1638 [c267, c1436, c133, c206, c205, c169] c1638 unsat1638 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c1436 := derived1436 a h
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1639 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨37, by decide⟩, true), (⟨3, by decide⟩, true), (⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨22, by decide⟩, true), (⟨8, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1152, some c14, some c41, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1639 : lratChecker f1639 p1639 = .success := by decide +kernel
theorem unsat1639 : Unsatisfiable (PosFin 57) f1639 := by
  apply lratCheckerSound f1639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1639
  · intro a ha; simp [p1639] at ha; subst a; trivial
  · exact checked1639
theorem derived1639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1639 := by
  apply localUnsat_implies_entails f1639 [c1152, c14, c41] c1639 unsat1639 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c14 := h 13 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1640 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨36, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨22, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c169, some c148, some c171, some c207, some c1639, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p1640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1640 : lratChecker f1640 p1640 = .success := by decide +kernel
theorem unsat1640 : Unsatisfiable (PosFin 57) f1640 := by
  apply lratCheckerSound f1640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1640
  · intro a ha; simp [p1640] at ha; subst a; trivial
  · exact checked1640
theorem derived1640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1640 := by
  apply localUnsat_implies_entails f1640 [c16, c169, c148, c171, c207, c1639] c1640 unsat1640 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c169 := h 168 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c171 := h 170 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c1639 := derived1639 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1641 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨37, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c117, some c145, some c218, some c209, some c54, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1641 : lratChecker f1641 p1641 = .success := by decide +kernel
theorem unsat1641 : Unsatisfiable (PosFin 57) f1641 := by
  apply lratCheckerSound f1641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1641
  · intro a ha; simp [p1641] at ha; subst a; trivial
  · exact checked1641
theorem derived1641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1641 := by
  apply localUnsat_implies_entails f1641 [c1569, c117, c145, c218, c209, c54] c1641 unsat1641 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c218 := h 217 (by decide)
  have h4 : Entails.eval a c209 := h 208 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1642 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨36, by decide⟩, true), (⟨13, by decide⟩, false), (⟨33, by decide⟩, false), (⟨39, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c267, some c127, some c1638, some c331, some c323, some c268, some c174, some c136, some c207, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1642 : lratChecker f1642 p1642 = .success := by decide +kernel
theorem unsat1642 : Unsatisfiable (PosFin 57) f1642 := by
  apply lratCheckerSound f1642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1642
  · intro a ha; simp [p1642] at ha; subst a; trivial
  · exact checked1642
theorem derived1642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1642 := by
  apply localUnsat_implies_entails f1642 [c631, c1628, c267, c127, c1638, c331, c323, c268, c174, c136, c207] c1642 unsat1642 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c1638 := derived1638 a h
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c174 := h 173 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1643 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1628, some c266, some c30, some c267, some c1635, some c1637, some c813, some c1641, some c1634, some c1642, some c1640, some c14, some c1434, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1643 : lratChecker f1643 p1643 = .success := by decide +kernel
theorem unsat1643 : Unsatisfiable (PosFin 57) f1643 := by
  apply lratCheckerSound f1643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1643
  · intro a ha; simp [p1643] at ha; subst a; trivial
  · exact checked1643
theorem derived1643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1643 := by
  apply localUnsat_implies_entails f1643 [c1569, c631, c1628, c266, c30, c267, c1635, c1637, c813, c1641, c1634, c1642, c1640, c14, c1434] c1643 unsat1643 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c1635 := derived1635 a h
  have h7 : Entails.eval a c1637 := derived1637 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c1641 := derived1641 a h
  have h10 : Entails.eval a c1634 := derived1634 a h
  have h11 : Entails.eval a c1642 := derived1642 a h
  have h12 : Entails.eval a c1640 := derived1640 a h
  have h13 : Entails.eval a c14 := h 13 (by decide)
  have h14 : Entails.eval a c1434 := derived1434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1644 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1628, some c266, some c30, some c1635, some c267, some c1637, some c813, some c1643, some c356, some c1243, some c18, some c38, some c1450, some c1156, some c58, some c1436, some c136, some c839, some c1139, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1644 : lratChecker f1644 p1644 = .success := by decide +kernel
theorem unsat1644 : Unsatisfiable (PosFin 57) f1644 := by
  apply lratCheckerSound f1644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1644
  · intro a ha; simp [p1644] at ha; subst a; trivial
  · exact checked1644
theorem derived1644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1644 := by
  apply localUnsat_implies_entails f1644 [c1569, c631, c1628, c266, c30, c1635, c267, c1637, c813, c1643, c356, c1243, c18, c38, c1450, c1156, c58, c1436, c136, c839, c1139] c1644 unsat1644 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1635 := derived1635 a h
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c1637 := derived1637 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c1643 := derived1643 a h
  have h10 : Entails.eval a c356 := h 355 (by decide)
  have h11 : Entails.eval a c1243 := derived1243 a h
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c38 := h 37 (by decide)
  have h14 : Entails.eval a c1450 := derived1450 a h
  have h15 : Entails.eval a c1156 := derived1156 a h
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c1436 := derived1436 a h
  have h18 : Entails.eval a c136 := h 135 (by decide)
  have h19 : Entails.eval a c839 := derived839 a h
  have h20 : Entails.eval a c1139 := derived1139 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1645 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c266, some c267, some c119, some c1636, some c359, some c356, some c1418, some c1137, some c229, some c1155, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1645 : lratChecker f1645 p1645 = .success := by decide +kernel
theorem unsat1645 : Unsatisfiable (PosFin 57) f1645 := by
  apply lratCheckerSound f1645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1645
  · intro a ha; simp [p1645] at ha; subst a; trivial
  · exact checked1645
theorem derived1645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1645 := by
  apply localUnsat_implies_entails f1645 [c631, c1628, c266, c267, c119, c1636, c359, c356, c1418, c1137, c229, c1155] c1645 unsat1645 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c1636 := derived1636 a h
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c1418 := derived1418 a h
  have h9 : Entails.eval a c1137 := derived1137 a h
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c1155 := derived1155 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1646 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨36, by decide⟩, true), (⟨13, by decide⟩, false), (⟨37, by decide⟩, true), (⟨39, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1628, some c631, some c1638, some c1642, some c268, some c1049, some c1414, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1646 : lratChecker f1646 p1646 = .success := by decide +kernel
theorem unsat1646 : Unsatisfiable (PosFin 57) f1646 := by
  apply lratCheckerSound f1646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1646
  · intro a ha; simp [p1646] at ha; subst a; trivial
  · exact checked1646
theorem derived1646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1646 := by
  apply localUnsat_implies_entails f1646 [c1569, c1628, c631, c1638, c1642, c268, c1049, c1414] c1646 unsat1646 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1638 := derived1638 a h
  have h4 : Entails.eval a c1642 := derived1642 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c1414 := derived1414 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1647 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1628, some c266, some c30, some c1635, some c1644, some c1645, some c813, some c1641, some c1646, some c1640, some c14, some c1434, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1647 : lratChecker f1647 p1647 = .success := by decide +kernel
theorem unsat1647 : Unsatisfiable (PosFin 57) f1647 := by
  apply lratCheckerSound f1647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1647
  · intro a ha; simp [p1647] at ha; subst a; trivial
  · exact checked1647
theorem derived1647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1647 := by
  apply localUnsat_implies_entails f1647 [c1569, c631, c1628, c266, c30, c1635, c1644, c1645, c813, c1641, c1646, c1640, c14, c1434] c1647 unsat1647 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c1635 := derived1635 a h
  have h6 : Entails.eval a c1644 := derived1644 a h
  have h7 : Entails.eval a c1645 := derived1645 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c1641 := derived1641 a h
  have h10 : Entails.eval a c1646 := derived1646 a h
  have h11 : Entails.eval a c1640 := derived1640 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c1434 := derived1434 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1648 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1635, some c631, some c1628, some c266, some c267, some c30, some c1644, some c1645, some c813, some c1641, some c1647, some c1418, some c1243, some c1154, some c14, some c21, some c41, some c1491, some c218, some c54, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1648 : lratChecker f1648 p1648 = .success := by decide +kernel
theorem unsat1648 : Unsatisfiable (PosFin 57) f1648 := by
  apply lratCheckerSound f1648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1648
  · intro a ha; simp [p1648] at ha; subst a; trivial
  · exact checked1648
theorem derived1648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1648 := by
  apply localUnsat_implies_entails f1648 [c1569, c1635, c631, c1628, c266, c267, c30, c1644, c1645, c813, c1641, c1647, c1418, c1243, c1154, c14, c21, c41, c1491, c218, c54] c1648 unsat1648 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1635 := derived1635 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1628 := derived1628 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c1644 := derived1644 a h
  have h8 : Entails.eval a c1645 := derived1645 a h
  have h9 : Entails.eval a c813 := derived813 a h
  have h10 : Entails.eval a c1641 := derived1641 a h
  have h11 : Entails.eval a c1647 := derived1647 a h
  have h12 : Entails.eval a c1418 := derived1418 a h
  have h13 : Entails.eval a c1243 := derived1243 a h
  have h14 : Entails.eval a c1154 := derived1154 a h
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c41 := h 40 (by decide)
  have h18 : Entails.eval a c1491 := derived1491 a h
  have h19 : Entails.eval a c218 := h 217 (by decide)
  have h20 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1649 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨19, by decide⟩, true), (⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c267, some c119, some c1282, some c266, some c212, some c54, some c53, some c316, some c318, some c40, some c1467, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1649 : lratChecker f1649 p1649 = .success := by decide +kernel
theorem unsat1649 : Unsatisfiable (PosFin 57) f1649 := by
  apply lratCheckerSound f1649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1649
  · intro a ha; simp [p1649] at ha; subst a; trivial
  · exact checked1649
theorem derived1649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1649 := by
  apply localUnsat_implies_entails f1649 [c1569, c267, c119, c1282, c266, c212, c54, c53, c316, c318, c40, c1467] c1649 unsat1649 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c1282 := derived1282 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c54 := h 53 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  have h8 : Entails.eval a c316 := h 315 (by decide)
  have h9 : Entails.eval a c318 := h 317 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c1467 := derived1467 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1650 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c148, some c16, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1650 : lratChecker f1650 p1650 = .success := by decide +kernel
theorem unsat1650 : Unsatisfiable (PosFin 57) f1650 := by
  apply lratCheckerSound f1650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1650
  · intro a ha; simp [p1650] at ha; subst a; trivial
  · exact checked1650
theorem derived1650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1650 := by
  apply localUnsat_implies_entails f1650 [c44, c148, c16] c1650 unsat1650 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c148 := h 147 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1651 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨32, by decide⟩, false), (⟨39, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1282, some c212, some c53, some c54, some c316, some c267, some c119, some c266, some c232, some c1649, some c525, some c268, some c28, some c40, some c144, some c14, some c13, some c138, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1651 : lratChecker f1651 p1651 = .success := by decide +kernel
theorem unsat1651 : Unsatisfiable (PosFin 57) f1651 := by
  apply lratCheckerSound f1651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1651
  · intro a ha; simp [p1651] at ha; subst a; trivial
  · exact checked1651
theorem derived1651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1651 := by
  apply localUnsat_implies_entails f1651 [c1569, c1282, c212, c53, c54, c316, c267, c119, c266, c232, c1649, c525, c268, c28, c40, c144, c14, c13, c138] c1651 unsat1651 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c212 := h 211 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c316 := h 315 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c232 := h 231 (by decide)
  have h10 : Entails.eval a c1649 := derived1649 a h
  have h11 : Entails.eval a c525 := derived525 a h
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c14 := h 13 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1652 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1282, some c267, some c119, some c1650, some c212, some c53, some c1651, some c216, some c356, some c229, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1652 : lratChecker f1652 p1652 = .success := by decide +kernel
theorem unsat1652 : Unsatisfiable (PosFin 57) f1652 := by
  apply lratCheckerSound f1652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1652
  · intro a ha; simp [p1652] at ha; subst a; trivial
  · exact checked1652
theorem derived1652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1652 := by
  apply localUnsat_implies_entails f1652 [c1569, c1282, c267, c119, c1650, c212, c53, c1651, c216, c356, c229] c1652 unsat1652 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c1650 := derived1650 a h
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c1651 := derived1651 a h
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1653 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨36, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1648, some c1282, some c1628, some c631, some c1436, some c1638, some c1466, some c1629, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1653 : lratChecker f1653 p1653 = .success := by decide +kernel
theorem unsat1653 : Unsatisfiable (PosFin 57) f1653 := by
  apply lratCheckerSound f1653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1653
  · intro a ha; simp [p1653] at ha; subst a; trivial
  · exact checked1653
theorem derived1653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1653 := by
  apply localUnsat_implies_entails f1653 [c1648, c1282, c1628, c631, c1436, c1638, c1466, c1629] c1653 unsat1653 (by rfl) a
  have h0 : Entails.eval a c1648 := derived1648 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1436 := derived1436 a h
  have h5 : Entails.eval a c1638 := derived1638 a h
  have h6 : Entails.eval a c1466 := derived1466 a h
  have h7 : Entails.eval a c1629 := derived1629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1654 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1648, some c1282, some c631, some c1628, some c1635, some c1652, some c813, some c1634, some c1653, some c1650, some c212, some c54, some c53, some c316, some c216, some c318, some c40, some c144, some c13, some c1236, some c1613, some c28, some c117, some c14, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1654 : lratChecker f1654 p1654 = .success := by decide +kernel
theorem unsat1654 : Unsatisfiable (PosFin 57) f1654 := by
  apply lratCheckerSound f1654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1654
  · intro a ha; simp [p1654] at ha; subst a; trivial
  · exact checked1654
theorem derived1654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1654 := by
  apply localUnsat_implies_entails f1654 [c1569, c1648, c1282, c631, c1628, c1635, c1652, c813, c1634, c1653, c1650, c212, c54, c53, c316, c216, c318, c40, c144, c13, c1236, c1613, c28, c117, c14] c1654 unsat1654 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1648 := derived1648 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1628 := derived1628 a h
  have h5 : Entails.eval a c1635 := derived1635 a h
  have h6 : Entails.eval a c1652 := derived1652 a h
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c1634 := derived1634 a h
  have h9 : Entails.eval a c1653 := derived1653 a h
  have h10 : Entails.eval a c1650 := derived1650 a h
  have h11 : Entails.eval a c212 := h 211 (by decide)
  have h12 : Entails.eval a c54 := h 53 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c40 := h 39 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c13 := h 12 (by decide)
  have h20 : Entails.eval a c1236 := derived1236 a h
  have h21 : Entails.eval a c1613 := derived1613 a h
  have h22 : Entails.eval a c28 := h 27 (by decide)
  have h23 : Entails.eval a c117 := h 116 (by decide)
  have h24 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1655 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1628, some c631, some c1635, some c1648, some c1282, some c1654, some c356, some c18, some c38, some c1466, some c216, some c148, some c1650, some c15, some c1436, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1655 : lratChecker f1655 p1655 = .success := by decide +kernel
theorem unsat1655 : Unsatisfiable (PosFin 57) f1655 := by
  apply lratCheckerSound f1655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1655
  · intro a ha; simp [p1655] at ha; subst a; trivial
  · exact checked1655
theorem derived1655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1655 := by
  apply localUnsat_implies_entails f1655 [c1628, c631, c1635, c1648, c1282, c1654, c356, c18, c38, c1466, c216, c148, c1650, c15, c1436] c1655 unsat1655 (by rfl) a
  have h0 : Entails.eval a c1628 := derived1628 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1635 := derived1635 a h
  have h3 : Entails.eval a c1648 := derived1648 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1654 := derived1654 a h
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c1466 := derived1466 a h
  have h10 : Entails.eval a c216 := h 215 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  have h12 : Entails.eval a c1650 := derived1650 a h
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c1436 := derived1436 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1656 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c266, some c267, some c36, some c1077, some c703, some c119, some c1637, some c123, some c1650, some c87, some c325, some c212, some c241, some c53, some c1156, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1656 : lratChecker f1656 p1656 = .success := by decide +kernel
theorem unsat1656 : Unsatisfiable (PosFin 57) f1656 := by
  apply lratCheckerSound f1656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1656
  · intro a ha; simp [p1656] at ha; subst a; trivial
  · exact checked1656
theorem derived1656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1656 := by
  apply localUnsat_implies_entails f1656 [c1569, c266, c267, c36, c1077, c703, c119, c1637, c123, c1650, c87, c325, c212, c241, c53, c1156] c1656 unsat1656 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c266 := h 265 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c703 := derived703 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c1637 := derived1637 a h
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c1650 := derived1650 a h
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c325 := h 324 (by decide)
  have h12 : Entails.eval a c212 := h 211 (by decide)
  have h13 : Entails.eval a c241 := h 240 (by decide)
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c1156 := derived1156 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1657 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1655, some c631, some c1628, some c266, some c267, some c36, some c112, some c22, some c1656, some c360, some c1507, some c1634, some c1491, some c897, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1657 : lratChecker f1657 p1657 = .success := by decide +kernel
theorem unsat1657 : Unsatisfiable (PosFin 57) f1657 := by
  apply lratCheckerSound f1657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1657
  · intro a ha; simp [p1657] at ha; subst a; trivial
  · exact checked1657
theorem derived1657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1657 := by
  apply localUnsat_implies_entails f1657 [c1655, c631, c1628, c266, c267, c36, c112, c22, c1656, c360, c1507, c1634, c1491, c897] c1657 unsat1657 (by rfl) a
  have h0 : Entails.eval a c1655 := derived1655 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1656 := derived1656 a h
  have h9 : Entails.eval a c360 := h 359 (by decide)
  have h10 : Entails.eval a c1507 := derived1507 a h
  have h11 : Entails.eval a c1634 := derived1634 a h
  have h12 : Entails.eval a c1491 := derived1491 a h
  have h13 : Entails.eval a c897 := derived897 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1658 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1655, some c1077, some c356, some c631, some c1628, some c266, some c267, some c36, some c22, some c112, some c1657, some c108, some c73, some c67, some c897, some c212, some c1491, some c1650, some c360, some c119, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1658 : lratChecker f1658 p1658 = .success := by decide +kernel
theorem unsat1658 : Unsatisfiable (PosFin 57) f1658 := by
  apply lratCheckerSound f1658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1658
  · intro a ha; simp [p1658] at ha; subst a; trivial
  · exact checked1658
theorem derived1658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1658 := by
  apply localUnsat_implies_entails f1658 [c1569, c1655, c1077, c356, c631, c1628, c266, c267, c36, c22, c112, c1657, c108, c73, c67, c897, c212, c1491, c1650, c360, c119] c1658 unsat1658 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1655 := derived1655 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1628 := derived1628 a h
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c1657 := derived1657 a h
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c897 := derived897 a h
  have h16 : Entails.eval a c212 := h 211 (by decide)
  have h17 : Entails.eval a c1491 := derived1491 a h
  have h18 : Entails.eval a c1650 := derived1650 a h
  have h19 : Entails.eval a c360 := h 359 (by decide)
  have h20 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1659 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1655, some c1658, some c1282, some c1495, some c1077, some c356, some c631, some c1628, some c266, some c267, some c23, some c1461, some c360, some c1629, some c1634, some c118, some c1633, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1659 : lratChecker f1659 p1659 = .success := by decide +kernel
theorem unsat1659 : Unsatisfiable (PosFin 57) f1659 := by
  apply lratCheckerSound f1659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1659
  · intro a ha; simp [p1659] at ha; subst a; trivial
  · exact checked1659
theorem derived1659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1659 := by
  apply localUnsat_implies_entails f1659 [c1655, c1658, c1282, c1495, c1077, c356, c631, c1628, c266, c267, c23, c1461, c360, c1629, c1634, c118, c1633] c1659 unsat1659 (by rfl) a
  have h0 : Entails.eval a c1655 := derived1655 a h
  have h1 : Entails.eval a c1658 := derived1658 a h
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c1495 := derived1495 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c1628 := derived1628 a h
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c1461 := derived1461 a h
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c1629 := derived1629 a h
  have h14 : Entails.eval a c1634 := derived1634 a h
  have h15 : Entails.eval a c118 := h 117 (by decide)
  have h16 : Entails.eval a c1633 := derived1633 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1660 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c112, some c1282, some c631, some c266, some c267, some c703, some c119, some c232, some c1650, some c212, some c150, some c53, some c216, some c316, some c28, some c40, some c525, some c1469, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1660 : lratChecker f1660 p1660 = .success := by decide +kernel
theorem unsat1660 : Unsatisfiable (PosFin 57) f1660 := by
  apply lratCheckerSound f1660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1660
  · intro a ha; simp [p1660] at ha; subst a; trivial
  · exact checked1660
theorem derived1660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1660 := by
  apply localUnsat_implies_entails f1660 [c1569, c112, c1282, c631, c266, c267, c703, c119, c232, c1650, c212, c150, c53, c216, c316, c28, c40, c525, c1469] c1660 unsat1660 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c1282 := derived1282 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c703 := derived703 a h
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c1650 := derived1650 a h
  have h10 : Entails.eval a c212 := h 211 (by decide)
  have h11 : Entails.eval a c150 := h 149 (by decide)
  have h12 : Entails.eval a c53 := h 52 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c316 := h 315 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  have h16 : Entails.eval a c40 := h 39 (by decide)
  have h17 : Entails.eval a c525 := derived525 a h
  have h18 : Entails.eval a c1469 := derived1469 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1661 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1436, some c1638, some c1629, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1661 : lratChecker f1661 p1661 = .success := by decide +kernel
theorem unsat1661 : Unsatisfiable (PosFin 57) f1661 := by
  apply lratCheckerSound f1661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1661
  · intro a ha; simp [p1661] at ha; subst a; trivial
  · exact checked1661
theorem derived1661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1661 := by
  apply localUnsat_implies_entails f1661 [c631, c1436, c1638, c1629] c1661 unsat1661 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1436 := derived1436 a h
  have h2 : Entails.eval a c1638 := derived1638 a h
  have h3 : Entails.eval a c1629 := derived1629 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1662 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c266, some c1655, some c1077, some c356, some c1658, some c1282, some c1495, some c1659, some c112, some c1660, some c360, some c21, some c41, some c1491, some c1661, some c11, some c16, some c150, some c169, some c218, some c319, some c134, some c40, some c13, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1662 : lratChecker f1662 p1662 = .success := by decide +kernel
theorem unsat1662 : Unsatisfiable (PosFin 57) f1662 := by
  apply lratCheckerSound f1662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1662
  · intro a ha; simp [p1662] at ha; subst a; trivial
  · exact checked1662
theorem derived1662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1662 := by
  apply localUnsat_implies_entails f1662 [c631, c1628, c266, c1655, c1077, c356, c1658, c1282, c1495, c1659, c112, c1660, c360, c21, c41, c1491, c1661, c11, c16, c150, c169, c218, c319, c134, c40, c13] c1662 unsat1662 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1655 := derived1655 a h
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c1658 := derived1658 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c1495 := derived1495 a h
  have h9 : Entails.eval a c1659 := derived1659 a h
  have h10 : Entails.eval a c112 := h 111 (by decide)
  have h11 : Entails.eval a c1660 := derived1660 a h
  have h12 : Entails.eval a c360 := h 359 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c41 := h 40 (by decide)
  have h15 : Entails.eval a c1491 := derived1491 a h
  have h16 : Entails.eval a c1661 := derived1661 a h
  have h17 : Entails.eval a c11 := h 10 (by decide)
  have h18 : Entails.eval a c16 := h 15 (by decide)
  have h19 : Entails.eval a c150 := h 149 (by decide)
  have h20 : Entails.eval a c169 := h 168 (by decide)
  have h21 : Entails.eval a c218 := h 217 (by decide)
  have h22 : Entails.eval a c319 := h 318 (by decide)
  have h23 : Entails.eval a c134 := h 133 (by decide)
  have h24 : Entails.eval a c40 := h 39 (by decide)
  have h25 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1663 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1662, some c631, some c1628, some c266, some c267, some c36, some c22, some c30, some c1590, some c358, some c354, some c1413, some c1573, some c1049, some c1641, some c1138, some c14, some c1154, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1663 : lratChecker f1663 p1663 = .success := by decide +kernel
theorem unsat1663 : Unsatisfiable (PosFin 57) f1663 := by
  apply lratCheckerSound f1663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1663
  · intro a ha; simp [p1663] at ha; subst a; trivial
  · exact checked1663
theorem derived1663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1663 := by
  apply localUnsat_implies_entails f1663 [c1569, c1662, c631, c1628, c266, c267, c36, c22, c30, c1590, c358, c354, c1413, c1573, c1049, c1641, c1138, c14, c1154] c1663 unsat1663 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1662 := derived1662 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1628 := derived1628 a h
  have h4 : Entails.eval a c266 := h 265 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c1590 := derived1590 a h
  have h10 : Entails.eval a c358 := h 357 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c1413 := derived1413 a h
  have h13 : Entails.eval a c1573 := derived1573 a h
  have h14 : Entails.eval a c1049 := derived1049 a h
  have h15 : Entails.eval a c1641 := derived1641 a h
  have h16 : Entails.eval a c1138 := derived1138 a h
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c1154 := derived1154 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1664 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1662, some c631, some c1628, some c266, some c267, some c1282, some c1590, some c236, some c1595, some c355, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1664 : lratChecker f1664 p1664 = .success := by decide +kernel
theorem unsat1664 : Unsatisfiable (PosFin 57) f1664 := by
  apply lratCheckerSound f1664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1664
  · intro a ha; simp [p1664] at ha; subst a; trivial
  · exact checked1664
theorem derived1664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1664 := by
  apply localUnsat_implies_entails f1664 [c1662, c631, c1628, c266, c267, c1282, c1590, c236, c1595, c355] c1664 unsat1664 (by rfl) a
  have h0 : Entails.eval a c1662 := derived1662 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1628 := derived1628 a h
  have h3 : Entails.eval a c266 := h 265 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c1282 := derived1282 a h
  have h6 : Entails.eval a c1590 := derived1590 a h
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c1595 := derived1595 a h
  have h9 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1665 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c1628, some c266, some c1662, some c1664, some c22, some c1663, some c358, some c1077, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1665 : lratChecker f1665 p1665 = .success := by decide +kernel
theorem unsat1665 : Unsatisfiable (PosFin 57) f1665 := by
  apply lratCheckerSound f1665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1665
  · intro a ha; simp [p1665] at ha; subst a; trivial
  · exact checked1665
theorem derived1665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1665 := by
  apply localUnsat_implies_entails f1665 [c631, c1628, c266, c1662, c1664, c22, c1663, c358, c1077] c1665 unsat1665 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c1628 := derived1628 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c1662 := derived1662 a h
  have h4 : Entails.eval a c1664 := derived1664 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c1663 := derived1663 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c1077 := derived1077 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1666 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c120, some c1665, some c70, some c71, some c39, some c19, some c1460, some c1450, some c16, some c357, some c233, some c271, some c235, some c813, some c119, some c147, some c219, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1666 : lratChecker f1666 p1666 = .success := by decide +kernel
theorem unsat1666 : Unsatisfiable (PosFin 57) f1666 := by
  apply lratCheckerSound f1666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1666
  · intro a ha; simp [p1666] at ha; subst a; trivial
  · exact checked1666
theorem derived1666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1666 := by
  apply localUnsat_implies_entails f1666 [c1569, c120, c1665, c70, c71, c39, c19, c1460, c1450, c16, c357, c233, c271, c235, c813, c119, c147, c219] c1666 unsat1666 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c1460 := derived1460 a h
  have h8 : Entails.eval a c1450 := derived1450 a h
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c357 := h 356 (by decide)
  have h11 : Entails.eval a c233 := h 232 (by decide)
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c235 := h 234 (by decide)
  have h14 : Entails.eval a c813 := derived813 a h
  have h15 : Entails.eval a c119 := h 118 (by decide)
  have h16 : Entails.eval a c147 := h 146 (by decide)
  have h17 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1667 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c70, some c71, some c39, some c19, some c120, some c1666, some c1372, some c8, some c602, some c271, some c268, some c1360, some c235, some c357, some c813, some c1479, some c280, some c16, some c219, some c133, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1667 : lratChecker f1667 p1667 = .success := by decide +kernel
theorem unsat1667 : Unsatisfiable (PosFin 57) f1667 := by
  apply lratCheckerSound f1667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1667
  · intro a ha; simp [p1667] at ha; subst a; trivial
  · exact checked1667
theorem derived1667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1667 := by
  apply localUnsat_implies_entails f1667 [c1569, c1665, c70, c71, c39, c19, c120, c1666, c1372, c8, c602, c271, c268, c1360, c235, c357, c813, c1479, c280, c16, c219, c133] c1667 unsat1667 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c1666 := derived1666 a h
  have h8 : Entails.eval a c1372 := derived1372 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c602 := derived602 a h
  have h11 : Entails.eval a c271 := h 270 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c1360 := derived1360 a h
  have h14 : Entails.eval a c235 := h 234 (by decide)
  have h15 : Entails.eval a c357 := h 356 (by decide)
  have h16 : Entails.eval a c813 := derived813 a h
  have h17 : Entails.eval a c1479 := derived1479 a h
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c16 := h 15 (by decide)
  have h20 : Entails.eval a c219 := h 218 (by decide)
  have h21 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1668 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1303, some c266, some c267, some c1450, some c357, some c1636, some c813, some c1641, some c1640, some c1638, some c268, some c213, some c1414, some c53, some c1491, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1668 : lratChecker f1668 p1668 = .success := by decide +kernel
theorem unsat1668 : Unsatisfiable (PosFin 57) f1668 := by
  apply lratCheckerSound f1668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1668
  · intro a ha; simp [p1668] at ha; subst a; trivial
  · exact checked1668
theorem derived1668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1668 := by
  apply localUnsat_implies_entails f1668 [c1569, c1303, c266, c267, c1450, c357, c1636, c813, c1641, c1640, c1638, c268, c213, c1414, c53, c1491] c1668 unsat1668 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c1450 := derived1450 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c1636 := derived1636 a h
  have h7 : Entails.eval a c813 := derived813 a h
  have h8 : Entails.eval a c1641 := derived1641 a h
  have h9 : Entails.eval a c1640 := derived1640 a h
  have h10 : Entails.eval a c1638 := derived1638 a h
  have h11 : Entails.eval a c268 := h 267 (by decide)
  have h12 : Entails.eval a c213 := h 212 (by decide)
  have h13 : Entails.eval a c1414 := derived1414 a h
  have h14 : Entails.eval a c53 := h 52 (by decide)
  have h15 : Entails.eval a c1491 := derived1491 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1669 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, false), (⟨19, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1636, some c357, some c1160, some c229, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1669 : lratChecker f1669 p1669 = .success := by decide +kernel
theorem unsat1669 : Unsatisfiable (PosFin 57) f1669 := by
  apply lratCheckerSound f1669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1669
  · intro a ha; simp [p1669] at ha; subst a; trivial
  · exact checked1669
theorem derived1669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1669 := by
  apply localUnsat_implies_entails f1669 [c1636, c357, c1160, c229] c1669 unsat1669 (by rfl) a
  have h0 : Entails.eval a c1636 := derived1636 a h
  have h1 : Entails.eval a c357 := h 356 (by decide)
  have h2 : Entails.eval a c1160 := derived1160 a h
  have h3 : Entails.eval a c229 := h 228 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1670 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c631, some c1665, some c19, some c66, some c70, some c1667, some c267, some c266, some c1303, some c39, some c71, some c1668, some c1669, some c813, some c1641, some c1640, some c1638, some c268, some c213, some c1414, some c1154, some c149, some c1491, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1670 : lratChecker f1670 p1670 = .success := by decide +kernel
theorem unsat1670 : Unsatisfiable (PosFin 57) f1670 := by
  apply lratCheckerSound f1670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1670
  · intro a ha; simp [p1670] at ha; subst a; trivial
  · exact checked1670
theorem derived1670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1670 := by
  apply localUnsat_implies_entails f1670 [c1569, c631, c1665, c19, c66, c70, c1667, c267, c266, c1303, c39, c71, c1668, c1669, c813, c1641, c1640, c1638, c268, c213, c1414, c1154, c149, c1491] c1670 unsat1670 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1665 := derived1665 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c1667 := derived1667 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c266 := h 265 (by decide)
  have h9 : Entails.eval a c1303 := derived1303 a h
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c1668 := derived1668 a h
  have h13 : Entails.eval a c1669 := derived1669 a h
  have h14 : Entails.eval a c813 := derived813 a h
  have h15 : Entails.eval a c1641 := derived1641 a h
  have h16 : Entails.eval a c1640 := derived1640 a h
  have h17 : Entails.eval a c1638 := derived1638 a h
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c213 := h 212 (by decide)
  have h20 : Entails.eval a c1414 := derived1414 a h
  have h21 : Entails.eval a c1154 := derived1154 a h
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c1491 := derived1491 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1671 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c66, some c71, some c39, some c19, some c631, some c70, some c1667, some c1668, some c1670, some c357, some c1149, some c1360, some c167, some c8, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1671 : lratChecker f1671 p1671 = .success := by decide +kernel
theorem unsat1671 : Unsatisfiable (PosFin 57) f1671 := by
  apply lratCheckerSound f1671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1671
  · intro a ha; simp [p1671] at ha; subst a; trivial
  · exact checked1671
theorem derived1671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1671 := by
  apply localUnsat_implies_entails f1671 [c1569, c1665, c66, c71, c39, c19, c631, c70, c1667, c1668, c1670, c357, c1149, c1360, c167, c8] c1671 unsat1671 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c66 := h 65 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c70 := h 69 (by decide)
  have h8 : Entails.eval a c1667 := derived1667 a h
  have h9 : Entails.eval a c1668 := derived1668 a h
  have h10 : Entails.eval a c1670 := derived1670 a h
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c1149 := derived1149 a h
  have h13 : Entails.eval a c1360 := derived1360 a h
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1672 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, true), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1479, some c813, some c1092, some c235, some c29, some c218, some c213, some c283, some c53, some c57, some c315, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1672 : lratChecker f1672 p1672 = .success := by decide +kernel
theorem unsat1672 : Unsatisfiable (PosFin 57) f1672 := by
  apply lratCheckerSound f1672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1672
  · intro a ha; simp [p1672] at ha; subst a; trivial
  · exact checked1672
theorem derived1672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1672 := by
  apply localUnsat_implies_entails f1672 [c1569, c1479, c813, c1092, c235, c29, c218, c213, c283, c53, c57, c315] c1672 unsat1672 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1479 := derived1479 a h
  have h2 : Entails.eval a c813 := derived813 a h
  have h3 : Entails.eval a c1092 := derived1092 a h
  have h4 : Entails.eval a c235 := h 234 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c213 := h 212 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1673 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c147, some c219, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1673 : lratChecker f1673 p1673 = .success := by decide +kernel
theorem unsat1673 : Unsatisfiable (PosFin 57) f1673 := by
  apply lratCheckerSound f1673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1673
  · intro a ha; simp [p1673] at ha; subst a; trivial
  · exact checked1673
theorem derived1673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1673 := by
  apply localUnsat_implies_entails f1673 [c119, c147, c219] c1673 unsat1673 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1674 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1282, some c1450, some c120, some c15, some c1672, some c16, some c1673, some c813, some c1092, some c235, some c1641, some c271, some c233, some c136, some c582, some c207, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1674 : lratChecker f1674 p1674 = .success := by decide +kernel
theorem unsat1674 : Unsatisfiable (PosFin 57) f1674 := by
  apply lratCheckerSound f1674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1674
  · intro a ha; simp [p1674] at ha; subst a; trivial
  · exact checked1674
theorem derived1674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1674 := by
  apply localUnsat_implies_entails f1674 [c1569, c1282, c1450, c120, c15, c1672, c16, c1673, c813, c1092, c235, c1641, c271, c233, c136, c582, c207] c1674 unsat1674 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1282 := derived1282 a h
  have h2 : Entails.eval a c1450 := derived1450 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c15 := h 14 (by decide)
  have h5 : Entails.eval a c1672 := derived1672 a h
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c1673 := derived1673 a h
  have h8 : Entails.eval a c813 := derived813 a h
  have h9 : Entails.eval a c1092 := derived1092 a h
  have h10 : Entails.eval a c235 := h 234 (by decide)
  have h11 : Entails.eval a c1641 := derived1641 a h
  have h12 : Entails.eval a c271 := h 270 (by decide)
  have h13 : Entails.eval a c233 := h 232 (by decide)
  have h14 : Entails.eval a c136 := h 135 (by decide)
  have h15 : Entails.eval a c582 := derived582 a h
  have h16 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1675 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨2, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c267, some c1479, some c29, some c813, some c213, some c53, some c57, some c212, some c313, some c283, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1675 : lratChecker f1675 p1675 = .success := by decide +kernel
theorem unsat1675 : Unsatisfiable (PosFin 57) f1675 := by
  apply lratCheckerSound f1675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1675
  · intro a ha; simp [p1675] at ha; subst a; trivial
  · exact checked1675
theorem derived1675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1675 := by
  apply localUnsat_implies_entails f1675 [c1569, c267, c1479, c29, c813, c213, c53, c57, c212, c313, c283] c1675 unsat1675 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c1479 := derived1479 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c813 := derived813 a h
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c212 := h 211 (by decide)
  have h9 : Entails.eval a c313 := h 312 (by decide)
  have h10 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1676 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨7, by decide⟩, false), (⟨24, by decide⟩, false), (⟨34, by decide⟩, false), (⟨6, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c267, some c119, some c236, some c1650, some c357, some c1651, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1676 : lratChecker f1676 p1676 = .success := by decide +kernel
theorem unsat1676 : Unsatisfiable (PosFin 57) f1676 := by
  apply lratCheckerSound f1676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1676
  · intro a ha; simp [p1676] at ha; subst a; trivial
  · exact checked1676
theorem derived1676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1676 := by
  apply localUnsat_implies_entails f1676 [c266, c267, c119, c236, c1650, c357, c1651] c1676 unsat1676 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c236 := h 235 (by decide)
  have h4 : Entails.eval a c1650 := derived1650 a h
  have h5 : Entails.eval a c357 := h 356 (by decide)
  have h6 : Entails.eval a c1651 := derived1651 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1677 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, false), (⟨40, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c16, some c208, some c167, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1677 : lratChecker f1677 p1677 = .success := by decide +kernel
theorem unsat1677 : Unsatisfiable (PosFin 57) f1677 := by
  apply lratCheckerSound f1677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1677
  · intro a ha; simp [p1677] at ha; subst a; trivial
  · exact checked1677
theorem derived1677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1677 := by
  apply localUnsat_implies_entails f1677 [c16, c208, c167] c1677 unsat1677 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1678 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1665, some c631, some c19, some c39, some c71, some c1671, some c1282, some c1450, some c1674, some c267, some c266, some c1675, some c1676, some c813, some c1641, some c1677, some c1436, some c1661, some c15, some c357, some c167, some c234, some c207, some c271, some c136, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1678 : lratChecker f1678 p1678 = .success := by decide +kernel
theorem unsat1678 : Unsatisfiable (PosFin 57) f1678 := by
  apply lratCheckerSound f1678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1678
  · intro a ha; simp [p1678] at ha; subst a; trivial
  · exact checked1678
theorem derived1678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1678 := by
  apply localUnsat_implies_entails f1678 [c1569, c1665, c631, c19, c39, c71, c1671, c1282, c1450, c1674, c267, c266, c1675, c1676, c813, c1641, c1677, c1436, c1661, c15, c357, c167, c234, c207, c271, c136] c1678 unsat1678 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1665 := derived1665 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1671 := derived1671 a h
  have h7 : Entails.eval a c1282 := derived1282 a h
  have h8 : Entails.eval a c1450 := derived1450 a h
  have h9 : Entails.eval a c1674 := derived1674 a h
  have h10 : Entails.eval a c267 := h 266 (by decide)
  have h11 : Entails.eval a c266 := h 265 (by decide)
  have h12 : Entails.eval a c1675 := derived1675 a h
  have h13 : Entails.eval a c1676 := derived1676 a h
  have h14 : Entails.eval a c813 := derived813 a h
  have h15 : Entails.eval a c1641 := derived1641 a h
  have h16 : Entails.eval a c1677 := derived1677 a h
  have h17 : Entails.eval a c1436 := derived1436 a h
  have h18 : Entails.eval a c1661 := derived1661 a h
  have h19 : Entails.eval a c15 := h 14 (by decide)
  have h20 : Entails.eval a c357 := h 356 (by decide)
  have h21 : Entails.eval a c167 := h 166 (by decide)
  have h22 : Entails.eval a c234 := h 233 (by decide)
  have h23 : Entails.eval a c207 := h 206 (by decide)
  have h24 : Entails.eval a c271 := h 270 (by decide)
  have h25 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1679 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c1678, some c1077, some c1665, some c631, some c1464, some c357, some c22, some c42, some c76, some c210, some c141, some c45, some c250, some c339, some c104, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1679 : lratChecker f1679 p1679 = .success := by decide +kernel
theorem unsat1679 : Unsatisfiable (PosFin 57) f1679 := by
  apply lratCheckerSound f1679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1679
  · intro a ha; simp [p1679] at ha; subst a; trivial
  · exact checked1679
theorem derived1679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1679 := by
  apply localUnsat_implies_entails f1679 [c1569, c1678, c1077, c1665, c631, c1464, c357, c22, c42, c76, c210, c141, c45, c250, c339, c104] c1679 unsat1679 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c1678 := derived1678 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1665 := derived1665 a h
  have h4 : Entails.eval a c631 := derived631 a h
  have h5 : Entails.eval a c1464 := derived1464 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c141 := h 140 (by decide)
  have h12 : Entails.eval a c45 := h 44 (by decide)
  have h13 : Entails.eval a c250 := h 249 (by decide)
  have h14 : Entails.eval a c339 := h 338 (by decide)
  have h15 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1680 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨15, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1569, some c119, some c147, some c265, some c211, some c34, some c28, some c45, some c53, some c250, some c215, some c50, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1680 : lratChecker f1680 p1680 = .success := by decide +kernel
theorem unsat1680 : Unsatisfiable (PosFin 57) f1680 := by
  apply lratCheckerSound f1680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1680
  · intro a ha; simp [p1680] at ha; subst a; trivial
  · exact checked1680
theorem derived1680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1680 := by
  apply localUnsat_implies_entails f1680 [c1569, c119, c147, c265, c211, c34, c28, c45, c53, c250, c215, c50] c1680 unsat1680 (by rfl) a
  have h0 : Entails.eval a c1569 := derived1569 a h
  have h1 : Entails.eval a c119 := h 118 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c211 := h 210 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c215 := h 214 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1681 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c268, some c28, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1681 : lratChecker f1681 p1681 = .success := by decide +kernel
theorem unsat1681 : Unsatisfiable (PosFin 57) f1681 := by
  apply lratCheckerSound f1681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1681
  · intro a ha; simp [p1681] at ha; subst a; trivial
  · exact checked1681
theorem derived1681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1681 := by
  apply localUnsat_implies_entails f1681 [c271, c268, c28] c1681 unsat1681 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1682 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨40, by decide⟩, true), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1665, some c231, some c120, some c24, some c1678, some c1077, some c631, some c1679, some c112, some c16, some c1680, some c1681, some c233, some c357, some c22, some c42, some c74, some c210, some c353, some c141, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1682 : lratChecker f1682 p1682 = .success := by decide +kernel
theorem unsat1682 : Unsatisfiable (PosFin 57) f1682 := by
  apply lratCheckerSound f1682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1682
  · intro a ha; simp [p1682] at ha; subst a; trivial
  · exact checked1682
theorem derived1682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1682 := by
  apply localUnsat_implies_entails f1682 [c1665, c231, c120, c24, c1678, c1077, c631, c1679, c112, c16, c1680, c1681, c233, c357, c22, c42, c74, c210, c353, c141] c1682 unsat1682 (by rfl) a
  have h0 : Entails.eval a c1665 := derived1665 a h
  have h1 : Entails.eval a c231 := h 230 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c1678 := derived1678 a h
  have h5 : Entails.eval a c1077 := derived1077 a h
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c1679 := derived1679 a h
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c16 := h 15 (by decide)
  have h10 : Entails.eval a c1680 := derived1680 a h
  have h11 : Entails.eval a c1681 := derived1681 a h
  have h12 : Entails.eval a c233 := h 232 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c74 := h 73 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c353 := h 352 (by decide)
  have h19 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1683 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨2, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c108, some c1077, some c631, some c1307, some c1313, some c1318, some c357, some c10, some c1414, some c1306, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1683 : lratChecker f1683 p1683 = .success := by decide +kernel
theorem unsat1683 : Unsatisfiable (PosFin 57) f1683 := by
  apply lratCheckerSound f1683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1683
  · intro a ha; simp [p1683] at ha; subst a; trivial
  · exact checked1683
theorem derived1683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1683 := by
  apply localUnsat_implies_entails f1683 [c108, c1077, c631, c1307, c1313, c1318, c357, c10, c1414, c1306] c1683 unsat1683 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c1307 := derived1307 a h
  have h4 : Entails.eval a c1313 := derived1313 a h
  have h5 : Entails.eval a c1318 := derived1318 a h
  have h6 : Entails.eval a c357 := h 356 (by decide)
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c1414 := derived1414 a h
  have h9 : Entails.eval a c1306 := derived1306 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1683

end CochromaticTwenty.Certificates.B16_4_2
