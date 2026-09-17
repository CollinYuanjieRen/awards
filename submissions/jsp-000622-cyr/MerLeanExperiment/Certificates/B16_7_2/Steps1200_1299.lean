import MerLeanExperiment.Certificates.B16_7_2.Steps1100_1199

/-! Generated from the actual pinned b16_7_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_7_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1589 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1588, some c1051, some c1444, some c35, some c1274, some c1242, some c89, some c92, some c384, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1589 : lratChecker f1589 p1589 = .success := by decide +kernel
theorem unsat1589 : Unsatisfiable (PosFin 57) f1589 := by
  apply lratCheckerSound f1589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1589
  · intro a ha; simp [p1589] at ha; subst a; trivial
  · exact checked1589
theorem derived1589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1589 := by
  apply localUnsat_implies_entails f1589 [c1588, c1051, c1444, c35, c1274, c1242, c89, c92, c384] c1589 unsat1589 (by rfl) a
  have h0 : Entails.eval a c1588 := derived1588 a h
  have h1 : Entails.eval a c1051 := derived1051 a h
  have h2 : Entails.eval a c1444 := derived1444 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c1274 := derived1274 a h
  have h5 : Entails.eval a c1242 := derived1242 a h
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c92 := h 91 (by decide)
  have h8 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1590 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨28, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c37, some c1501, some c318, some c276, some c1582, some c108, some c13, some c110, some c150, some c31, some c199, some c229, some c352, some c353, some c158, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1590 : lratChecker f1590 p1590 = .success := by decide +kernel
theorem unsat1590 : Unsatisfiable (PosFin 57) f1590 := by
  apply lratCheckerSound f1590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1590
  · intro a ha; simp [p1590] at ha; subst a; trivial
  · exact checked1590
theorem derived1590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1590 := by
  apply localUnsat_implies_entails f1590 [c44, c37, c1501, c318, c276, c1582, c108, c13, c110, c150, c31, c199, c229, c352, c353, c158] c1590 unsat1590 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c1501 := derived1501 a h
  have h3 : Entails.eval a c318 := h 317 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c1582 := derived1582 a h
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c199 := h 198 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1591 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1589, some c57, some c37, some c64, some c44, some c1567, some c1590, some c51, some c1545, some c1577, some c89, some c85, some c381, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1591 : lratChecker f1591 p1591 = .success := by decide +kernel
theorem unsat1591 : Unsatisfiable (PosFin 57) f1591 := by
  apply lratCheckerSound f1591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1591
  · intro a ha; simp [p1591] at ha; subst a; trivial
  · exact checked1591
theorem derived1591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1591 := by
  apply localUnsat_implies_entails f1591 [c1486, c1587, c1589, c57, c37, c64, c44, c1567, c1590, c51, c1545, c1577, c89, c85, c381] c1591 unsat1591 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1589 := derived1589 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c1567 := derived1567 a h
  have h8 : Entails.eval a c1590 := derived1590 a h
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c1545 := derived1545 a h
  have h11 : Entails.eval a c1577 := derived1577 a h
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  have h14 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1592 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨12, by decide⟩, true), (⟨51, by decide⟩, false), (⟨45, by decide⟩, false), (⟨13, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c366, some c387, some c74, some c357, some c165, some c183, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1592 : lratChecker f1592 p1592 = .success := by decide +kernel
theorem unsat1592 : Unsatisfiable (PosFin 57) f1592 := by
  apply lratCheckerSound f1592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1592
  · intro a ha; simp [p1592] at ha; subst a; trivial
  · exact checked1592
theorem derived1592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1592 := by
  apply localUnsat_implies_entails f1592 [c1486, c366, c387, c74, c357, c165, c183] c1592 unsat1592 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c387 := h 386 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1593 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1589, some c1591, some c1051, some c1145, some c1444, some c117, some c217, some c42, some c35, some c12, some c1592, some c1242, some c1264, some c39, some c89, some c337, some c1061, some c1260, some c224, some c252, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1593 : lratChecker f1593 p1593 = .success := by decide +kernel
theorem unsat1593 : Unsatisfiable (PosFin 57) f1593 := by
  apply lratCheckerSound f1593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1593
  · intro a ha; simp [p1593] at ha; subst a; trivial
  · exact checked1593
theorem derived1593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1593 := by
  apply localUnsat_implies_entails f1593 [c1486, c1587, c1589, c1591, c1051, c1145, c1444, c117, c217, c42, c35, c12, c1592, c1242, c1264, c39, c89, c337, c1061, c1260, c224, c252] c1593 unsat1593 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1589 := derived1589 a h
  have h3 : Entails.eval a c1591 := derived1591 a h
  have h4 : Entails.eval a c1051 := derived1051 a h
  have h5 : Entails.eval a c1145 := derived1145 a h
  have h6 : Entails.eval a c1444 := derived1444 a h
  have h7 : Entails.eval a c117 := h 116 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c12 := h 11 (by decide)
  have h12 : Entails.eval a c1592 := derived1592 a h
  have h13 : Entails.eval a c1242 := derived1242 a h
  have h14 : Entails.eval a c1264 := derived1264 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c337 := h 336 (by decide)
  have h18 : Entails.eval a c1061 := derived1061 a h
  have h19 : Entails.eval a c1260 := derived1260 a h
  have h20 : Entails.eval a c224 := h 223 (by decide)
  have h21 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1594 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, false), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c102, some c1495, some c51, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1594 : lratChecker f1594 p1594 = .success := by decide +kernel
theorem unsat1594 : Unsatisfiable (PosFin 57) f1594 := by
  apply lratCheckerSound f1594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1594
  · intro a ha; simp [p1594] at ha; subst a; trivial
  · exact checked1594
theorem derived1594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1594 := by
  apply localUnsat_implies_entails f1594 [c102, c1495, c51] c1594 unsat1594 (by rfl) a
  have h0 : Entails.eval a c102 := h 101 (by decide)
  have h1 : Entails.eval a c1495 := derived1495 a h
  have h2 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1595 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1593, some c102, some c1594, some c1051, some c1444, some c42, some c47, some c1359, some c315, some c39, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1595 : lratChecker f1595 p1595 = .success := by decide +kernel
theorem unsat1595 : Unsatisfiable (PosFin 57) f1595 := by
  apply lratCheckerSound f1595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1595
  · intro a ha; simp [p1595] at ha; subst a; trivial
  · exact checked1595
theorem derived1595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1595 := by
  apply localUnsat_implies_entails f1595 [c1486, c1587, c1593, c102, c1594, c1051, c1444, c42, c47, c1359, c315, c39] c1595 unsat1595 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1593 := derived1593 a h
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c1594 := derived1594 a h
  have h5 : Entails.eval a c1051 := derived1051 a h
  have h6 : Entails.eval a c1444 := derived1444 a h
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c1359 := derived1359 a h
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1596 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c48, some c43, some c313, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1596 : lratChecker f1596 p1596 = .success := by decide +kernel
theorem unsat1596 : Unsatisfiable (PosFin 57) f1596 := by
  apply lratCheckerSound f1596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1596
  · intro a ha; simp [p1596] at ha; subst a; trivial
  · exact checked1596
theorem derived1596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1596 := by
  apply localUnsat_implies_entails f1596 [c1486, c48, c43, c313] c1596 unsat1596 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1597 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1596, some c1283, some c296, some c45, some c56, some c274, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1597 : lratChecker f1597 p1597 = .success := by decide +kernel
theorem unsat1597 : Unsatisfiable (PosFin 57) f1597 := by
  apply lratCheckerSound f1597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1597
  · intro a ha; simp [p1597] at ha; subst a; trivial
  · exact checked1597
theorem derived1597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1597 := by
  apply localUnsat_implies_entails f1597 [c1596, c1283, c296, c45, c56, c274] c1597 unsat1597 (by rfl) a
  have h0 : Entails.eval a c1596 := derived1596 a h
  have h1 : Entails.eval a c1283 := derived1283 a h
  have h2 : Entails.eval a c296 := h 295 (by decide)
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1598 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨32, by decide⟩, false), (⟨28, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c296, some c319, some c1587, some c1597, some c274, some c317, some c276, some c216, some c329, some c1552, some c292, some c42, some c73, some c285, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1598 : lratChecker f1598 p1598 = .success := by decide +kernel
theorem unsat1598 : Unsatisfiable (PosFin 57) f1598 := by
  apply lratCheckerSound f1598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1598
  · intro a ha; simp [p1598] at ha; subst a; trivial
  · exact checked1598
theorem derived1598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1598 := by
  apply localUnsat_implies_entails f1598 [c1486, c296, c319, c1587, c1597, c274, c317, c276, c216, c329, c1552, c292, c42, c73, c285] c1598 unsat1598 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c1587 := derived1587 a h
  have h4 : Entails.eval a c1597 := derived1597 a h
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c317 := h 316 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c329 := h 328 (by decide)
  have h10 : Entails.eval a c1552 := derived1552 a h
  have h11 : Entails.eval a c292 := h 291 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1599 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨28, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1598, some c45, some c41, some c315, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1599 : lratChecker f1599 p1599 = .success := by decide +kernel
theorem unsat1599 : Unsatisfiable (PosFin 57) f1599 := by
  apply lratCheckerSound f1599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1599
  · intro a ha; simp [p1599] at ha; subst a; trivial
  · exact checked1599
theorem derived1599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1599 := by
  apply localUnsat_implies_entails f1599 [c1486, c1587, c1598, c45, c41, c315] c1599 unsat1599 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1598 := derived1598 a h
  have h3 : Entails.eval a c45 := h 44 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1600 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨28, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1595, some c296, some c319, some c274, some c317, some c216, some c29, some c1552, some c110, some c206, some c35, some c13, some c267, some c1592, some c117, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1600 : lratChecker f1600 p1600 = .success := by decide +kernel
theorem unsat1600 : Unsatisfiable (PosFin 57) f1600 := by
  apply lratCheckerSound f1600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1600
  · intro a ha; simp [p1600] at ha; subst a; trivial
  · exact checked1600
theorem derived1600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1600 := by
  apply localUnsat_implies_entails f1600 [c1595, c296, c319, c274, c317, c216, c29, c1552, c110, c206, c35, c13, c267, c1592, c117] c1600 unsat1600 (by rfl) a
  have h0 : Entails.eval a c1595 := derived1595 a h
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c274 := h 273 (by decide)
  have h4 : Entails.eval a c317 := h 316 (by decide)
  have h5 : Entails.eval a c216 := h 215 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c1552 := derived1552 a h
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c1592 := derived1592 a h
  have h14 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1601 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c45, some c41, some c313, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1601 : lratChecker f1601 p1601 = .success := by decide +kernel
theorem unsat1601 : Unsatisfiable (PosFin 57) f1601 := by
  apply lratCheckerSound f1601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1601
  · intro a ha; simp [p1601] at ha; subst a; trivial
  · exact checked1601
theorem derived1601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1601 := by
  apply localUnsat_implies_entails f1601 [c1486, c45, c41, c313] c1601 unsat1601 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1602 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1595, some c57, some c64, some c1597, some c1601, some c319, some c296, some c1599, some c1600, some c274, some c317, some c88, some c216, some c29, some c1552, some c110, some c47, some c15, some c1203, some c13, some c340, some c161, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1602 : lratChecker f1602 p1602 = .success := by decide +kernel
theorem unsat1602 : Unsatisfiable (PosFin 57) f1602 := by
  apply lratCheckerSound f1602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1602
  · intro a ha; simp [p1602] at ha; subst a; trivial
  · exact checked1602
theorem derived1602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1602 := by
  apply localUnsat_implies_entails f1602 [c1587, c1595, c57, c64, c1597, c1601, c319, c296, c1599, c1600, c274, c317, c88, c216, c29, c1552, c110, c47, c15, c1203, c13, c340, c161] c1602 unsat1602 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1595 := derived1595 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c1597 := derived1597 a h
  have h5 : Entails.eval a c1601 := derived1601 a h
  have h6 : Entails.eval a c319 := h 318 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c1599 := derived1599 a h
  have h9 : Entails.eval a c1600 := derived1600 a h
  have h10 : Entails.eval a c274 := h 273 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c216 := h 215 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c1552 := derived1552 a h
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c47 := h 46 (by decide)
  have h18 : Entails.eval a c15 := h 14 (by decide)
  have h19 : Entails.eval a c1203 := derived1203 a h
  have h20 : Entails.eval a c13 := h 12 (by decide)
  have h21 : Entails.eval a c340 := h 339 (by decide)
  have h22 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1603 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, true), (⟨53, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c33, some c1557, some c381, some c39, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1603 : lratChecker f1603 p1603 = .success := by decide +kernel
theorem unsat1603 : Unsatisfiable (PosFin 57) f1603 := by
  apply lratCheckerSound f1603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1603
  · intro a ha; simp [p1603] at ha; subst a; trivial
  · exact checked1603
theorem derived1603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1603 := by
  apply localUnsat_implies_entails f1603 [c1486, c1587, c33, c1557, c381, c39] c1603 unsat1603 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c1557 := derived1557 a h
  have h4 : Entails.eval a c381 := h 380 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1604 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1595, some c57, some c64, some c1597, some c1601, some c1501, some c318, some c276, some c1603, some c313, some c285, some c39, some c73, some c381, some c292, some c85, some c220, some c1577, some c31, some c230, some c212, some c258, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1604 : lratChecker f1604 p1604 = .success := by decide +kernel
theorem unsat1604 : Unsatisfiable (PosFin 57) f1604 := by
  apply lratCheckerSound f1604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1604
  · intro a ha; simp [p1604] at ha; subst a; trivial
  · exact checked1604
theorem derived1604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1604 := by
  apply localUnsat_implies_entails f1604 [c1486, c1587, c1595, c57, c64, c1597, c1601, c1501, c318, c276, c1603, c313, c285, c39, c73, c381, c292, c85, c220, c1577, c31, c230, c212, c258] c1604 unsat1604 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1595 := derived1595 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c1597 := derived1597 a h
  have h6 : Entails.eval a c1601 := derived1601 a h
  have h7 : Entails.eval a c1501 := derived1501 a h
  have h8 : Entails.eval a c318 := h 317 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c1603 := derived1603 a h
  have h11 : Entails.eval a c313 := h 312 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c381 := h 380 (by decide)
  have h16 : Entails.eval a c292 := h 291 (by decide)
  have h17 : Entails.eval a c85 := h 84 (by decide)
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c1577 := derived1577 a h
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c230 := h 229 (by decide)
  have h22 : Entails.eval a c212 := h 211 (by decide)
  have h23 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1605 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨32, by decide⟩, true), (⟨53, by decide⟩, false), (⟨28, by decide⟩, true), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1597, some c1601, some c33, some c1603, some c1550, some c275, some c1545, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1605 : lratChecker f1605 p1605 = .success := by decide +kernel
theorem unsat1605 : Unsatisfiable (PosFin 57) f1605 := by
  apply lratCheckerSound f1605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1605
  · intro a ha; simp [p1605] at ha; subst a; trivial
  · exact checked1605
theorem derived1605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1605 := by
  apply localUnsat_implies_entails f1605 [c1486, c1587, c1597, c1601, c33, c1603, c1550, c275, c1545] c1605 unsat1605 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1597 := derived1597 a h
  have h3 : Entails.eval a c1601 := derived1601 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c1603 := derived1603 a h
  have h6 : Entails.eval a c1550 := derived1550 a h
  have h7 : Entails.eval a c275 := h 274 (by decide)
  have h8 : Entails.eval a c1545 := derived1545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1606 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1602, some c1587, some c1595, some c57, some c64, some c1597, some c1601, some c1604, some c1605, some c313, some c39, some c701, some c381, some c40, some c85, some c1545, some c1577, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1606 : lratChecker f1606 p1606 = .success := by decide +kernel
theorem unsat1606 : Unsatisfiable (PosFin 57) f1606 := by
  apply lratCheckerSound f1606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1606
  · intro a ha; simp [p1606] at ha; subst a; trivial
  · exact checked1606
theorem derived1606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1606 := by
  apply localUnsat_implies_entails f1606 [c1486, c1602, c1587, c1595, c57, c64, c1597, c1601, c1604, c1605, c313, c39, c701, c381, c40, c85, c1545, c1577] c1606 unsat1606 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1602 := derived1602 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1595 := derived1595 a h
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c1597 := derived1597 a h
  have h7 : Entails.eval a c1601 := derived1601 a h
  have h8 : Entails.eval a c1604 := derived1604 a h
  have h9 : Entails.eval a c1605 := derived1605 a h
  have h10 : Entails.eval a c313 := h 312 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c701 := derived701 a h
  have h13 : Entails.eval a c381 := h 380 (by decide)
  have h14 : Entails.eval a c40 := h 39 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c1545 := derived1545 a h
  have h17 : Entails.eval a c1577 := derived1577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1607 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, true), (⟨8, by decide⟩, false), (⟨50, by decide⟩, false), (⟨53, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨45, by decide⟩, false), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1577, some c33, some c1557, some c1515, some c136, some c13, some c118, some c138, some c1465, some c246, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1607 : lratChecker f1607 p1607 = .success := by decide +kernel
theorem unsat1607 : Unsatisfiable (PosFin 57) f1607 := by
  apply lratCheckerSound f1607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1607
  · intro a ha; simp [p1607] at ha; subst a; trivial
  · exact checked1607
theorem derived1607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1607 := by
  apply localUnsat_implies_entails f1607 [c1486, c1577, c33, c1557, c1515, c136, c13, c118, c138, c1465, c246] c1607 unsat1607 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1577 := derived1577 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c1557 := derived1557 a h
  have h4 : Entails.eval a c1515 := derived1515 a h
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c1465 := derived1465 a h
  have h10 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1608 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1606, some c88, some c1602, some c1587, some c1595, some c57, some c64, some c1597, some c1601, some c1501, some c318, some c276, some c1577, some c1607, some c313, some c285, some c73, some c292, some c220, some c31, some c110, some c212, some c230, some c15, some c13, some c268, some c161, some c226, some c352, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1608 : lratChecker f1608 p1608 = .success := by decide +kernel
theorem unsat1608 : Unsatisfiable (PosFin 57) f1608 := by
  apply lratCheckerSound f1608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1608
  · intro a ha; simp [p1608] at ha; subst a; trivial
  · exact checked1608
theorem derived1608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1608 := by
  apply localUnsat_implies_entails f1608 [c1486, c1606, c88, c1602, c1587, c1595, c57, c64, c1597, c1601, c1501, c318, c276, c1577, c1607, c313, c285, c73, c292, c220, c31, c110, c212, c230, c15, c13, c268, c161, c226, c352] c1608 unsat1608 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1606 := derived1606 a h
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c1602 := derived1602 a h
  have h4 : Entails.eval a c1587 := derived1587 a h
  have h5 : Entails.eval a c1595 := derived1595 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c1597 := derived1597 a h
  have h9 : Entails.eval a c1601 := derived1601 a h
  have h10 : Entails.eval a c1501 := derived1501 a h
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c1577 := derived1577 a h
  have h14 : Entails.eval a c1607 := derived1607 a h
  have h15 : Entails.eval a c313 := h 312 (by decide)
  have h16 : Entails.eval a c285 := h 284 (by decide)
  have h17 : Entails.eval a c73 := h 72 (by decide)
  have h18 : Entails.eval a c292 := h 291 (by decide)
  have h19 : Entails.eval a c220 := h 219 (by decide)
  have h20 : Entails.eval a c31 := h 30 (by decide)
  have h21 : Entails.eval a c110 := h 109 (by decide)
  have h22 : Entails.eval a c212 := h 211 (by decide)
  have h23 : Entails.eval a c230 := h 229 (by decide)
  have h24 : Entails.eval a c15 := h 14 (by decide)
  have h25 : Entails.eval a c13 := h 12 (by decide)
  have h26 : Entails.eval a c268 := h 267 (by decide)
  have h27 : Entails.eval a c161 := h 160 (by decide)
  have h28 : Entails.eval a c226 := h 225 (by decide)
  have h29 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1609 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨32, by decide⟩, true), (⟨50, by decide⟩, false), (⟨28, by decide⟩, true), (⟨4, by decide⟩, false), (⟨34, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1545, some c1577, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1609 : lratChecker f1609 p1609 = .success := by decide +kernel
theorem unsat1609 : Unsatisfiable (PosFin 57) f1609 := by
  apply lratCheckerSound f1609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1609
  · intro a ha; simp [p1609] at ha; subst a; trivial
  · exact checked1609
theorem derived1609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1609 := by
  apply localUnsat_implies_entails f1609 [c1545, c1577] c1609 unsat1609 (by rfl) a
  have h0 : Entails.eval a c1545 := derived1545 a h
  have h1 : Entails.eval a c1577 := derived1577 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1610 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1595, some c1601, some c57, some c64, some c1597, some c1602, some c1606, some c88, some c1608, some c1609, some c71, some c40, some c340, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1610 : lratChecker f1610 p1610 = .success := by decide +kernel
theorem unsat1610 : Unsatisfiable (PosFin 57) f1610 := by
  apply lratCheckerSound f1610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1610
  · intro a ha; simp [p1610] at ha; subst a; trivial
  · exact checked1610
theorem derived1610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1610 := by
  apply localUnsat_implies_entails f1610 [c1587, c1595, c1601, c57, c64, c1597, c1602, c1606, c88, c1608, c1609, c71, c40, c340] c1610 unsat1610 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1595 := derived1595 a h
  have h2 : Entails.eval a c1601 := derived1601 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c1597 := derived1597 a h
  have h6 : Entails.eval a c1602 := derived1602 a h
  have h7 : Entails.eval a c1606 := derived1606 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c1608 := derived1608 a h
  have h10 : Entails.eval a c1609 := derived1609 a h
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c340 := h 339 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1611 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1051, some c1444, some c42, some c35, some c313, some c39, some c1242, some c388, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1611 : lratChecker f1611 p1611 = .success := by decide +kernel
theorem unsat1611 : Unsatisfiable (PosFin 57) f1611 := by
  apply lratCheckerSound f1611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1611
  · intro a ha; simp [p1611] at ha; subst a; trivial
  · exact checked1611
theorem derived1611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1611 := by
  apply localUnsat_implies_entails f1611 [c1486, c1051, c1444, c42, c35, c313, c39, c1242, c388] c1611 unsat1611 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1051 := derived1051 a h
  have h2 : Entails.eval a c1444 := derived1444 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c1242 := derived1242 a h
  have h8 : Entails.eval a c388 := h 387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1612 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1295, some c1286, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1612 : lratChecker f1612 p1612 = .success := by decide +kernel
theorem unsat1612 : Unsatisfiable (PosFin 57) f1612 := by
  apply lratCheckerSound f1612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1612
  · intro a ha; simp [p1612] at ha; subst a; trivial
  · exact checked1612
theorem derived1612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1612 := by
  apply localUnsat_implies_entails f1612 [c1295, c1286] c1612 unsat1612 (by rfl) a
  have h0 : Entails.eval a c1295 := derived1295 a h
  have h1 : Entails.eval a c1286 := derived1286 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1613 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1595, some c1611, some c1610, some c102, some c101, some c1612, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1613 : lratChecker f1613 p1613 = .success := by decide +kernel
theorem unsat1613 : Unsatisfiable (PosFin 57) f1613 := by
  apply lratCheckerSound f1613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1613
  · intro a ha; simp [p1613] at ha; subst a; trivial
  · exact checked1613
theorem derived1613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1613 := by
  apply localUnsat_implies_entails f1613 [c1587, c1595, c1611, c1610, c102, c101, c1612] c1613 unsat1613 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1595 := derived1595 a h
  have h2 : Entails.eval a c1611 := derived1611 a h
  have h3 : Entails.eval a c1610 := derived1610 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c1612 := derived1612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1614 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1613, some c1587, some c65, some c61, some c349, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1614 : lratChecker f1614 p1614 = .success := by decide +kernel
theorem unsat1614 : Unsatisfiable (PosFin 57) f1614 := by
  apply lratCheckerSound f1614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1614
  · intro a ha; simp [p1614] at ha; subst a; trivial
  · exact checked1614
theorem derived1614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1614 := by
  apply localUnsat_implies_entails f1614 [c1486, c1613, c1587, c65, c61, c349] c1614 unsat1614 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1615 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1594, some c1614, some c44, some c1613, some c1573, some c37, some c1576, some c85, some c1567, some c1590, some c51, some c1609, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1615 : lratChecker f1615 p1615 = .success := by decide +kernel
theorem unsat1615 : Unsatisfiable (PosFin 57) f1615 := by
  apply lratCheckerSound f1615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1615
  · intro a ha; simp [p1615] at ha; subst a; trivial
  · exact checked1615
theorem derived1615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1615 := by
  apply localUnsat_implies_entails f1615 [c1486, c1594, c1614, c44, c1613, c1573, c37, c1576, c85, c1567, c1590, c51, c1609] c1615 unsat1615 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1594 := derived1594 a h
  have h2 : Entails.eval a c1614 := derived1614 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c1613 := derived1613 a h
  have h5 : Entails.eval a c1573 := derived1573 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c1576 := derived1576 a h
  have h8 : Entails.eval a c85 := h 84 (by decide)
  have h9 : Entails.eval a c1567 := derived1567 a h
  have h10 : Entails.eval a c1590 := derived1590 a h
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c1609 := derived1609 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1616 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1613, some c1587, some c37, some c1594, some c1573, some c44, some c1614, some c1615, some c76, some c1581, some c1590, some c51, some c1609, some c89, some c85, some c381, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1616 : lratChecker f1616 p1616 = .success := by decide +kernel
theorem unsat1616 : Unsatisfiable (PosFin 57) f1616 := by
  apply lratCheckerSound f1616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1616
  · intro a ha; simp [p1616] at ha; subst a; trivial
  · exact checked1616
theorem derived1616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1616 := by
  apply localUnsat_implies_entails f1616 [c1486, c1613, c1587, c37, c1594, c1573, c44, c1614, c1615, c76, c1581, c1590, c51, c1609, c89, c85, c381] c1616 unsat1616 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1594 := derived1594 a h
  have h5 : Entails.eval a c1573 := derived1573 a h
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c1614 := derived1614 a h
  have h8 : Entails.eval a c1615 := derived1615 a h
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c1581 := derived1581 a h
  have h11 : Entails.eval a c1590 := derived1590 a h
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c1609 := derived1609 a h
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c85 := h 84 (by decide)
  have h16 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1617 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1051, some c1444, some c35, some c1242, some c1264, some c89, some c337, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1617 : lratChecker f1617 p1617 = .success := by decide +kernel
theorem unsat1617 : Unsatisfiable (PosFin 57) f1617 := by
  apply lratCheckerSound f1617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1617
  · intro a ha; simp [p1617] at ha; subst a; trivial
  · exact checked1617
theorem derived1617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1617 := by
  apply localUnsat_implies_entails f1617 [c1051, c1444, c35, c1242, c1264, c89, c337] c1617 unsat1617 (by rfl) a
  have h0 : Entails.eval a c1051 := derived1051 a h
  have h1 : Entails.eval a c1444 := derived1444 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c1242 := derived1242 a h
  have h4 : Entails.eval a c1264 := derived1264 a h
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c337 := h 336 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1618 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1616, some c1051, some c1444, some c35, some c1145, some c109, some c1613, some c1587, some c342, some c1274, some c387, some c388, some c62, some c12, some c188, some c333, some c183, some c193, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1618 : lratChecker f1618 p1618 = .success := by decide +kernel
theorem unsat1618 : Unsatisfiable (PosFin 57) f1618 := by
  apply lratCheckerSound f1618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1618
  · intro a ha; simp [p1618] at ha; subst a; trivial
  · exact checked1618
theorem derived1618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1618 := by
  apply localUnsat_implies_entails f1618 [c1486, c1616, c1051, c1444, c35, c1145, c109, c1613, c1587, c342, c1274, c387, c388, c62, c12, c188, c333, c183, c193] c1618 unsat1618 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1616 := derived1616 a h
  have h2 : Entails.eval a c1051 := derived1051 a h
  have h3 : Entails.eval a c1444 := derived1444 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c1145 := derived1145 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1613 := derived1613 a h
  have h8 : Entails.eval a c1587 := derived1587 a h
  have h9 : Entails.eval a c342 := h 341 (by decide)
  have h10 : Entails.eval a c1274 := derived1274 a h
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c388 := h 387 (by decide)
  have h13 : Entails.eval a c62 := h 61 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c188 := h 187 (by decide)
  have h16 : Entails.eval a c333 := h 332 (by decide)
  have h17 : Entails.eval a c183 := h 182 (by decide)
  have h18 : Entails.eval a c193 := h 192 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1619 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1613, some c1587, some c1616, some c1618, some c1264, some c356, some c355, some c68, some c101, some c1614, some c1617, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1619 : lratChecker f1619 p1619 = .success := by decide +kernel
theorem unsat1619 : Unsatisfiable (PosFin 57) f1619 := by
  apply lratCheckerSound f1619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1619
  · intro a ha; simp [p1619] at ha; subst a; trivial
  · exact checked1619
theorem derived1619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1619 := by
  apply localUnsat_implies_entails f1619 [c1613, c1587, c1616, c1618, c1264, c356, c355, c68, c101, c1614, c1617] c1619 unsat1619 (by rfl) a
  have h0 : Entails.eval a c1613 := derived1613 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1616 := derived1616 a h
  have h3 : Entails.eval a c1618 := derived1618 a h
  have h4 : Entails.eval a c1264 := derived1264 a h
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c1614 := derived1614 a h
  have h10 : Entails.eval a c1617 := derived1617 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1620 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1619, some c1611, some c1613, some c1514, some c1596, some c269, some c280, some c63, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1620 : lratChecker f1620 p1620 = .success := by decide +kernel
theorem unsat1620 : Unsatisfiable (PosFin 57) f1620 := by
  apply lratCheckerSound f1620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1620
  · intro a ha; simp [p1620] at ha; subst a; trivial
  · exact checked1620
theorem derived1620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1620 := by
  apply localUnsat_implies_entails f1620 [c1486, c1587, c1619, c1611, c1613, c1514, c1596, c269, c280, c63] c1620 unsat1620 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1619 := derived1619 a h
  have h3 : Entails.eval a c1611 := derived1611 a h
  have h4 : Entails.eval a c1613 := derived1613 a h
  have h5 : Entails.eval a c1514 := derived1514 a h
  have h6 : Entails.eval a c1596 := derived1596 a h
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1621 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1613, some c1619, some c1276, some c59, some c298, some c370, some c39, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1621 : lratChecker f1621 p1621 = .success := by decide +kernel
theorem unsat1621 : Unsatisfiable (PosFin 57) f1621 := by
  apply lratCheckerSound f1621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1621
  · intro a ha; simp [p1621] at ha; subst a; trivial
  · exact checked1621
theorem derived1621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1621 := by
  apply localUnsat_implies_entails f1621 [c1587, c1613, c1619, c1276, c59, c298, c370, c39] c1621 unsat1621 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1613 := derived1613 a h
  have h2 : Entails.eval a c1619 := derived1619 a h
  have h3 : Entails.eval a c1276 := derived1276 a h
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c298 := h 297 (by decide)
  have h6 : Entails.eval a c370 := h 369 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1622 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨42, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1620, some c1614, some c1587, some c1619, some c1601, some c1613, some c319, some c280, some c317, some c290, some c1560, some c216, some c313, some c29, some c1552, some c39, some c747, some c35, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1622 : lratChecker f1622 p1622 = .success := by decide +kernel
theorem unsat1622 : Unsatisfiable (PosFin 57) f1622 := by
  apply lratCheckerSound f1622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1622
  · intro a ha; simp [p1622] at ha; subst a; trivial
  · exact checked1622
theorem derived1622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1622 := by
  apply localUnsat_implies_entails f1622 [c1620, c1614, c1587, c1619, c1601, c1613, c319, c280, c317, c290, c1560, c216, c313, c29, c1552, c39, c747, c35] c1622 unsat1622 (by rfl) a
  have h0 : Entails.eval a c1620 := derived1620 a h
  have h1 : Entails.eval a c1614 := derived1614 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1619 := derived1619 a h
  have h4 : Entails.eval a c1601 := derived1601 a h
  have h5 : Entails.eval a c1613 := derived1613 a h
  have h6 : Entails.eval a c319 := h 318 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c290 := h 289 (by decide)
  have h10 : Entails.eval a c1560 := derived1560 a h
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c313 := h 312 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c1552 := derived1552 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c747 := derived747 a h
  have h17 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1623 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1619, some c1611, some c1621, some c76, some c1622, some c1620, some c1614, some c1601, some c1613, some c1501, some c318, some c276, some c292, some c220, some c31, some c110, some c15, some c13, some c136, some c161, some c344, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1623 : lratChecker f1623 p1623 = .success := by decide +kernel
theorem unsat1623 : Unsatisfiable (PosFin 57) f1623 := by
  apply lratCheckerSound f1623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1623
  · intro a ha; simp [p1623] at ha; subst a; trivial
  · exact checked1623
theorem derived1623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1623 := by
  apply localUnsat_implies_entails f1623 [c1587, c1619, c1611, c1621, c76, c1622, c1620, c1614, c1601, c1613, c1501, c318, c276, c292, c220, c31, c110, c15, c13, c136, c161, c344] c1623 unsat1623 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1619 := derived1619 a h
  have h2 : Entails.eval a c1611 := derived1611 a h
  have h3 : Entails.eval a c1621 := derived1621 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c1622 := derived1622 a h
  have h6 : Entails.eval a c1620 := derived1620 a h
  have h7 : Entails.eval a c1614 := derived1614 a h
  have h8 : Entails.eval a c1601 := derived1601 a h
  have h9 : Entails.eval a c1613 := derived1613 a h
  have h10 : Entails.eval a c1501 := derived1501 a h
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c31 := h 30 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c136 := h 135 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1624 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c89, some c85, some c381, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1624 : lratChecker f1624 p1624 = .success := by decide +kernel
theorem unsat1624 : Unsatisfiable (PosFin 57) f1624 := by
  apply lratCheckerSound f1624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1624
  · intro a ha; simp [p1624] at ha; subst a; trivial
  · exact checked1624
theorem derived1624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1624 := by
  apply localUnsat_implies_entails f1624 [c1486, c89, c85, c381] c1624 unsat1624 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c381 := h 380 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1625 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1620, some c1614, some c1587, some c1619, some c1601, some c1611, some c1621, some c76, some c1622, some c1623, some c1624, some c1609, some c1551, some c40, some c39, some c701, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1625 : lratChecker f1625 p1625 = .success := by decide +kernel
theorem unsat1625 : Unsatisfiable (PosFin 57) f1625 := by
  apply lratCheckerSound f1625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1625
  · intro a ha; simp [p1625] at ha; subst a; trivial
  · exact checked1625
theorem derived1625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1625 := by
  apply localUnsat_implies_entails f1625 [c1620, c1614, c1587, c1619, c1601, c1611, c1621, c76, c1622, c1623, c1624, c1609, c1551, c40, c39, c701] c1625 unsat1625 (by rfl) a
  have h0 : Entails.eval a c1620 := derived1620 a h
  have h1 : Entails.eval a c1614 := derived1614 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1619 := derived1619 a h
  have h4 : Entails.eval a c1601 := derived1601 a h
  have h5 : Entails.eval a c1611 := derived1611 a h
  have h6 : Entails.eval a c1621 := derived1621 a h
  have h7 : Entails.eval a c76 := h 75 (by decide)
  have h8 : Entails.eval a c1622 := derived1622 a h
  have h9 : Entails.eval a c1623 := derived1623 a h
  have h10 : Entails.eval a c1624 := derived1624 a h
  have h11 : Entails.eval a c1609 := derived1609 a h
  have h12 : Entails.eval a c1551 := derived1551 a h
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c701 := derived701 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1626 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1587, some c1619, some c1611, some c76, some c77, some c73, some c373, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1626 : lratChecker f1626 p1626 = .success := by decide +kernel
theorem unsat1626 : Unsatisfiable (PosFin 57) f1626 := by
  apply lratCheckerSound f1626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1626
  · intro a ha; simp [p1626] at ha; subst a; trivial
  · exact checked1626
theorem derived1626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1626 := by
  apply localUnsat_implies_entails f1626 [c1486, c1587, c1619, c1611, c76, c77, c73, c373] c1626 unsat1626 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1587 := derived1587 a h
  have h2 : Entails.eval a c1619 := derived1619 a h
  have h3 : Entails.eval a c1611 := derived1611 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1627 : DefaultClause 57 := directClause [(⟨32, by decide⟩, false), (⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1627 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1626, some c1622, some c1587, some c1619, some c1611, some c1625, some c88, some c1620, some c1614, some c1601, some c1501, some c318, some c276, some c292, some c220, some c31, some c110, some c15, some c13, some c136, some c161, some c338, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1627 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1627 : lratChecker f1627 p1627 = .success := by decide +kernel
theorem unsat1627 : Unsatisfiable (PosFin 57) f1627 := by
  apply lratCheckerSound f1627 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1627
  · intro a ha; simp [p1627] at ha; subst a; trivial
  · exact checked1627
theorem derived1627 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1627 := by
  apply localUnsat_implies_entails f1627 [c1626, c1622, c1587, c1619, c1611, c1625, c88, c1620, c1614, c1601, c1501, c318, c276, c292, c220, c31, c110, c15, c13, c136, c161, c338] c1627 unsat1627 (by rfl) a
  have h0 : Entails.eval a c1626 := derived1626 a h
  have h1 : Entails.eval a c1622 := derived1622 a h
  have h2 : Entails.eval a c1587 := derived1587 a h
  have h3 : Entails.eval a c1619 := derived1619 a h
  have h4 : Entails.eval a c1611 := derived1611 a h
  have h5 : Entails.eval a c1625 := derived1625 a h
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c1620 := derived1620 a h
  have h8 : Entails.eval a c1614 := derived1614 a h
  have h9 : Entails.eval a c1601 := derived1601 a h
  have h10 : Entails.eval a c1501 := derived1501 a h
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c292 := h 291 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c31 := h 30 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  have h17 : Entails.eval a c15 := h 14 (by decide)
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c136 := h 135 (by decide)
  have h20 : Entails.eval a c161 := h 160 (by decide)
  have h21 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1628 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1628 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1619, some c1611, some c1601, some c1614, some c1620, some c1625, some c88, some c1626, some c1622, some c1627, some c1609, some c1551, some c40, some c39, some c701, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1628 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1628 : lratChecker f1628 p1628 = .success := by decide +kernel
theorem unsat1628 : Unsatisfiable (PosFin 57) f1628 := by
  apply lratCheckerSound f1628 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1628
  · intro a ha; simp [p1628] at ha; subst a; trivial
  · exact checked1628
theorem derived1628 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1628 := by
  apply localUnsat_implies_entails f1628 [c1587, c1619, c1611, c1601, c1614, c1620, c1625, c88, c1626, c1622, c1627, c1609, c1551, c40, c39, c701] c1628 unsat1628 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1619 := derived1619 a h
  have h2 : Entails.eval a c1611 := derived1611 a h
  have h3 : Entails.eval a c1601 := derived1601 a h
  have h4 : Entails.eval a c1614 := derived1614 a h
  have h5 : Entails.eval a c1620 := derived1620 a h
  have h6 : Entails.eval a c1625 := derived1625 a h
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c1626 := derived1626 a h
  have h9 : Entails.eval a c1622 := derived1622 a h
  have h10 : Entails.eval a c1627 := derived1627 a h
  have h11 : Entails.eval a c1609 := derived1609 a h
  have h12 : Entails.eval a c1551 := derived1551 a h
  have h13 : Entails.eval a c40 := h 39 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c701 := derived701 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1629 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1629 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1587, some c1619, some c1611, some c1628, some c102, some c101, some c1612, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1629 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1629 : lratChecker f1629 p1629 = .success := by decide +kernel
theorem unsat1629 : Unsatisfiable (PosFin 57) f1629 := by
  apply lratCheckerSound f1629 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1629
  · intro a ha; simp [p1629] at ha; subst a; trivial
  · exact checked1629
theorem derived1629 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1629 := by
  apply localUnsat_implies_entails f1629 [c1587, c1619, c1611, c1628, c102, c101, c1612] c1629 unsat1629 (by rfl) a
  have h0 : Entails.eval a c1587 := derived1587 a h
  have h1 : Entails.eval a c1619 := derived1619 a h
  have h2 : Entails.eval a c1611 := derived1611 a h
  have h3 : Entails.eval a c1628 := derived1628 a h
  have h4 : Entails.eval a c102 := h 101 (by decide)
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c1612 := derived1612 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1630 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨28, by decide⟩, false), (⟨34, by decide⟩, false), (⟨29, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1630 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c70, some c57, some c353, some c296, some c56, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1630 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1630 : lratChecker f1630 p1630 = .success := by decide +kernel
theorem unsat1630 : Unsatisfiable (PosFin 57) f1630 := by
  apply lratCheckerSound f1630 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1630
  · intro a ha; simp [p1630] at ha; subst a; trivial
  · exact checked1630
theorem derived1630 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1630 := by
  apply localUnsat_implies_entails f1630 [c1629, c70, c57, c353, c296, c56] c1630 unsat1630 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1631 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1631 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c44, some c37, some c50, some c70, some c58, some c291, some c76, some c73, some c1576, some c286, some c33, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1631 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1631 : lratChecker f1631 p1631 = .success := by decide +kernel
theorem unsat1631 : Unsatisfiable (PosFin 57) f1631 := by
  apply lratCheckerSound f1631 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1631
  · intro a ha; simp [p1631] at ha; subst a; trivial
  · exact checked1631
theorem derived1631 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1631 := by
  apply localUnsat_implies_entails f1631 [c1629, c1486, c44, c37, c50, c70, c58, c291, c76, c73, c1576, c286, c33] c1631 unsat1631 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c1576 := derived1576 a h
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1632 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1632 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c50, some c37, some c44, some c1631, some c275, some c64, some c61, some c333, some c270, some c33, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1632 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1632 : lratChecker f1632 p1632 = .success := by decide +kernel
theorem unsat1632 : Unsatisfiable (PosFin 57) f1632 := by
  apply lratCheckerSound f1632 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1632
  · intro a ha; simp [p1632] at ha; subst a; trivial
  · exact checked1632
theorem derived1632 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1632 := by
  apply localUnsat_implies_entails f1632 [c1629, c1486, c50, c37, c44, c1631, c275, c64, c61, c333, c270, c33] c1632 unsat1632 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c1631 := derived1631 a h
  have h6 : Entails.eval a c275 := h 274 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c270 := h 269 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1633 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1633 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c339, some c85, some c357, some c334, some c53, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1633 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1633 : lratChecker f1633 p1633 = .success := by decide +kernel
theorem unsat1633 : Unsatisfiable (PosFin 57) f1633 := by
  apply lratCheckerSound f1633 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1633
  · intro a ha; simp [p1633] at ha; subst a; trivial
  · exact checked1633
theorem derived1633 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1633 := by
  apply localUnsat_implies_entails f1633 [c1486, c339, c85, c357, c334, c53] c1633 unsat1633 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c339 := h 338 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c334 := h 333 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1634 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨34, by decide⟩, false), (⟨29, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1634 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c275, some c41, some c285, some c270, some c53, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1634 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1634 : lratChecker f1634 p1634 = .success := by decide +kernel
theorem unsat1634 : Unsatisfiable (PosFin 57) f1634 := by
  apply lratCheckerSound f1634 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1634
  · intro a ha; simp [p1634] at ha; subst a; trivial
  · exact checked1634
theorem derived1634 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1634 := by
  apply localUnsat_implies_entails f1634 [c1486, c275, c41, c285, c270, c53] c1634 unsat1634 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c275 := h 274 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1635 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1635 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1632, some c70, some c57, some c1634, some c38, some c339, some c1633, some c88, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1635 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1635 : lratChecker f1635 p1635 = .success := by decide +kernel
theorem unsat1635 : Unsatisfiable (PosFin 57) f1635 := by
  apply lratCheckerSound f1635 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1635
  · intro a ha; simp [p1635] at ha; subst a; trivial
  · exact checked1635
theorem derived1635 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1635 := by
  apply localUnsat_implies_entails f1635 [c1629, c1632, c70, c57, c1634, c38, c339, c1633, c88] c1635 unsat1635 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1632 := derived1632 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c1634 := derived1634 a h
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c339 := h 338 (by decide)
  have h7 : Entails.eval a c1633 := derived1633 a h
  have h8 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1636 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1636 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1576, some c33, some c269, some c285, some c53, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1636 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1636 : lratChecker f1636 p1636 = .success := by decide +kernel
theorem unsat1636 : Unsatisfiable (PosFin 57) f1636 := by
  apply lratCheckerSound f1636 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1636
  · intro a ha; simp [p1636] at ha; subst a; trivial
  · exact checked1636
theorem derived1636 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1636 := by
  apply localUnsat_implies_entails f1636 [c1486, c1576, c33, c269, c285, c53] c1636 unsat1636 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1576 := derived1576 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1637 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨42, by decide⟩, false), (⟨46, by decide⟩, false), (⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1637 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c363, some c85, some c333, some c358, some c53, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1637 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1637 : lratChecker f1637 p1637 = .success := by decide +kernel
theorem unsat1637 : Unsatisfiable (PosFin 57) f1637 := by
  apply lratCheckerSound f1637 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1637
  · intro a ha; simp [p1637] at ha; subst a; trivial
  · exact checked1637
theorem derived1637 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1637 := by
  apply localUnsat_implies_entails f1637 [c1486, c363, c85, c333, c358, c53] c1637 unsat1637 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c363 := h 362 (by decide)
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c333 := h 332 (by decide)
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1638 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1638 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c269, some c286, some c53, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1638 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1638 : lratChecker f1638 p1638 = .success := by decide +kernel
theorem unsat1638 : Unsatisfiable (PosFin 57) f1638 := by
  apply lratCheckerSound f1638 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1638
  · intro a ha; simp [p1638] at ha; subst a; trivial
  · exact checked1638
theorem derived1638 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1638 := by
  apply localUnsat_implies_entails f1638 [c1486, c269, c286, c53] c1638 unsat1638 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c286 := h 285 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1639 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1639 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1632, some c1636, some c82, some c76, some c1637, some c38, some c1638, some c291, some c41, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1639 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1639 : lratChecker f1639 p1639 = .success := by decide +kernel
theorem unsat1639 : Unsatisfiable (PosFin 57) f1639 := by
  apply lratCheckerSound f1639 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1639
  · intro a ha; simp [p1639] at ha; subst a; trivial
  · exact checked1639
theorem derived1639 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1639 := by
  apply localUnsat_implies_entails f1639 [c1629, c1486, c1632, c1636, c82, c76, c1637, c38, c1638, c291, c41] c1639 unsat1639 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1636 := derived1636 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c1637 := derived1637 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c1638 := derived1638 a h
  have h9 : Entails.eval a c291 := h 290 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1640 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1640 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1632, some c1635, some c1639, some c94, some c88, some c339, some c58, some c363, some c76, some c73, some c285, some c358, some c33, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1640 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1640 : lratChecker f1640 p1640 = .success := by decide +kernel
theorem unsat1640 : Unsatisfiable (PosFin 57) f1640 := by
  apply lratCheckerSound f1640 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1640
  · intro a ha; simp [p1640] at ha; subst a; trivial
  · exact checked1640
theorem derived1640 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1640 := by
  apply localUnsat_implies_entails f1640 [c1629, c1486, c1632, c1635, c1639, c94, c88, c339, c58, c363, c76, c73, c285, c358, c33] c1640 unsat1640 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1635 := derived1635 a h
  have h4 : Entails.eval a c1639 := derived1639 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c339 := h 338 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c363 := h 362 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1641 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1641 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1632, some c1640, some c54, some c64, some c61, some c1639, some c269, some c94, some c88, some c33, some c363, some c334, some c58, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1641 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1641 : lratChecker f1641 p1641 = .success := by decide +kernel
theorem unsat1641 : Unsatisfiable (PosFin 57) f1641 := by
  apply lratCheckerSound f1641 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1641
  · intro a ha; simp [p1641] at ha; subst a; trivial
  · exact checked1641
theorem derived1641 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1641 := by
  apply localUnsat_implies_entails f1641 [c1629, c1486, c1632, c1640, c54, c64, c61, c1639, c269, c94, c88, c33, c363, c334, c58] c1641 unsat1641 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1632 := derived1632 a h
  have h3 : Entails.eval a c1640 := derived1640 a h
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c1639 := derived1639 a h
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c363 := h 362 (by decide)
  have h13 : Entails.eval a c334 := h 333 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1642 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1642 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1641, some c1051, some c1444, some c35, some c908, some c1617, some c1624, some c388, some c337, some c96, some c66, some c339, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1642 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1642 : lratChecker f1642 p1642 = .success := by decide +kernel
theorem unsat1642 : Unsatisfiable (PosFin 57) f1642 := by
  apply lratCheckerSound f1642 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1642
  · intro a ha; simp [p1642] at ha; subst a; trivial
  · exact checked1642
theorem derived1642 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1642 := by
  apply localUnsat_implies_entails f1642 [c1629, c1641, c1051, c1444, c35, c908, c1617, c1624, c388, c337, c96, c66, c339] c1642 unsat1642 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1641 := derived1641 a h
  have h2 : Entails.eval a c1051 := derived1051 a h
  have h3 : Entails.eval a c1444 := derived1444 a h
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c908 := derived908 a h
  have h6 : Entails.eval a c1617 := derived1617 a h
  have h7 : Entails.eval a c1624 := derived1624 a h
  have h8 : Entails.eval a c388 := h 387 (by decide)
  have h9 : Entails.eval a c337 := h 336 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1643 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1643 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c1641, some c908, some c1051, some c1444, some c46, some c42, some c1642, some c61, some c65, some c270, some c349, some c271, some c1378, some c39, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1643 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1643 : lratChecker f1643 p1643 = .success := by decide +kernel
theorem unsat1643 : Unsatisfiable (PosFin 57) f1643 := by
  apply lratCheckerSound f1643 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1643
  · intro a ha; simp [p1643] at ha; subst a; trivial
  · exact checked1643
theorem derived1643 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1643 := by
  apply localUnsat_implies_entails f1643 [c1486, c1629, c1641, c908, c1051, c1444, c46, c42, c1642, c61, c65, c270, c349, c271, c1378, c39] c1643 unsat1643 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1641 := derived1641 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c1051 := derived1051 a h
  have h5 : Entails.eval a c1444 := derived1444 a h
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c1642 := derived1642 a h
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c1378 := derived1378 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1644 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨52, by decide⟩, true), (⟨7, by decide⟩, false), (⟨55, by decide⟩, true), (⟨8, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1644 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c188, some c161, some c16, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1644 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1644 : lratChecker f1644 p1644 = .success := by decide +kernel
theorem unsat1644 : Unsatisfiable (PosFin 57) f1644 := by
  apply lratCheckerSound f1644 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1644
  · intro a ha; simp [p1644] at ha; subst a; trivial
  · exact checked1644
theorem derived1644 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1644 := by
  apply localUnsat_implies_entails f1644 [c188, c161, c16] c1644 unsat1644 (by rfl) a
  have h0 : Entails.eval a c188 := h 187 (by decide)
  have h1 : Entails.eval a c161 := h 160 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1645 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨8, by decide⟩, false), (⟨26, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1645 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c163, some c144, some c8, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1645 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1645 : lratChecker f1645 p1645 = .success := by decide +kernel
theorem unsat1645 : Unsatisfiable (PosFin 57) f1645 := by
  apply lratCheckerSound f1645 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1645
  · intro a ha; simp [p1645] at ha; subst a; trivial
  · exact checked1645
theorem derived1645 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1645 := by
  apply localUnsat_implies_entails f1645 [c1643, c163, c144, c8] c1645 unsat1645 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1646 : DefaultClause 57 := directClause [(⟨44, by decide⟩, false), (⟨7, by decide⟩, false), (⟨55, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1646 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c368, some c176, some c1644, some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1646 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1646 : lratChecker f1646 p1646 = .success := by decide +kernel
theorem unsat1646 : Unsatisfiable (PosFin 57) f1646 := by
  apply lratCheckerSound f1646 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1646
  · intro a ha; simp [p1646] at ha; subst a; trivial
  · exact checked1646
theorem derived1646 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1646 := by
  apply localUnsat_implies_entails f1646 [c368, c176, c1644] c1646 unsat1646 (by rfl) a
  have h0 : Entails.eval a c368 := h 367 (by decide)
  have h1 : Entails.eval a c176 := h 175 (by decide)
  have h2 : Entails.eval a c1644 := derived1644 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1647 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨13, by decide⟩, false), (⟨8, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1647 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1629, some c1486, some c381, some c357, some c53, some c334, some c96, some c1646, some c56, some c100, some c90, some c74, some c366, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1647 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1647 : lratChecker f1647 p1647 = .success := by decide +kernel
theorem unsat1647 : Unsatisfiable (PosFin 57) f1647 := by
  apply lratCheckerSound f1647 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1647
  · intro a ha; simp [p1647] at ha; subst a; trivial
  · exact checked1647
theorem derived1647 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1647 := by
  apply localUnsat_implies_entails f1647 [c1643, c1629, c1486, c381, c357, c53, c334, c96, c1646, c56, c100, c90, c74, c366] c1647 unsat1647 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1486 := derived1486 a h
  have h3 : Entails.eval a c381 := h 380 (by decide)
  have h4 : Entails.eval a c357 := h 356 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c334 := h 333 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c1646 := derived1646 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c74 := h 73 (by decide)
  have h13 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1648 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨29, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1648 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1486, some c1629, some c37, some c50, some c70, some c57, some c354, some c353, some c275, some c71, some c1645, some c1647, some c33, some c508, some c270, some c286, some c63, some c100, some c86, some c78, some c366, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1648 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1648 : lratChecker f1648 p1648 = .success := by decide +kernel
theorem unsat1648 : Unsatisfiable (PosFin 57) f1648 := by
  apply lratCheckerSound f1648 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1648
  · intro a ha; simp [p1648] at ha; subst a; trivial
  · exact checked1648
theorem derived1648 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1648 := by
  apply localUnsat_implies_entails f1648 [c1643, c1486, c1629, c37, c50, c70, c57, c354, c353, c275, c71, c1645, c1647, c33, c508, c270, c286, c63, c100, c86, c78, c366] c1648 unsat1648 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c353 := h 352 (by decide)
  have h9 : Entails.eval a c275 := h 274 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c1645 := derived1645 a h
  have h12 : Entails.eval a c1647 := derived1647 a h
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c508 := derived508 a h
  have h15 : Entails.eval a c270 := h 269 (by decide)
  have h16 : Entails.eval a c286 := h 285 (by decide)
  have h17 : Entails.eval a c63 := h 62 (by decide)
  have h18 : Entails.eval a c100 := h 99 (by decide)
  have h19 : Entails.eval a c86 := h 85 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1649 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1649 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1576, some c87, some c344, some c368, some c56, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1649 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1649 : lratChecker f1649 p1649 = .success := by decide +kernel
theorem unsat1649 : Unsatisfiable (PosFin 57) f1649 := by
  apply lratCheckerSound f1649 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1649
  · intro a ha; simp [p1649] at ha; subst a; trivial
  · exact checked1649
theorem derived1649 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1649 := by
  apply localUnsat_implies_entails f1649 [c1486, c1576, c87, c344, c368, c56] c1649 unsat1649 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1576 := derived1576 a h
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c344 := h 343 (by decide)
  have h4 : Entails.eval a c368 := h 367 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1650 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1650 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1643, some c1576, some c1649, some c100, some c86, some c366, some c342, some c55, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1650 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1650 : lratChecker f1650 p1650 = .success := by decide +kernel
theorem unsat1650 : Unsatisfiable (PosFin 57) f1650 := by
  apply lratCheckerSound f1650 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1650
  · intro a ha; simp [p1650] at ha; subst a; trivial
  · exact checked1650
theorem derived1650 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1650 := by
  apply localUnsat_implies_entails f1650 [c1486, c1643, c1576, c1649, c100, c86, c366, c342, c55] c1650 unsat1650 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1643 := derived1643 a h
  have h2 : Entails.eval a c1576 := derived1576 a h
  have h3 : Entails.eval a c1649 := derived1649 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c342 := h 341 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1651 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨25, by decide⟩, true), (⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨53, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1651 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c201, some c204, some c245, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1651 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1651 : lratChecker f1651 p1651 = .success := by decide +kernel
theorem unsat1651 : Unsatisfiable (PosFin 57) f1651 := by
  apply lratCheckerSound f1651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1651
  · intro a ha; simp [p1651] at ha; subst a; trivial
  · exact checked1651
theorem derived1651 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1651 := by
  apply localUnsat_implies_entails f1651 [c201, c204, c245] c1651 unsat1651 (by rfl) a
  have h0 : Entails.eval a c201 := h 200 (by decide)
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1652 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨26, by decide⟩, true), (⟨4, by decide⟩, true), (⟨29, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1652 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1643, some c37, some c1648, some c1650, some c82, some c50, some c333, some c53, some c63, some c286, some c374, some c355, some c353, some c43, some c83, some c62, some c297, some c1651, some c21, some c24, some c226, some c241, some c265, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1652 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1652 : lratChecker f1652 p1652 = .success := by decide +kernel
theorem unsat1652 : Unsatisfiable (PosFin 57) f1652 := by
  apply lratCheckerSound f1652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1652
  · intro a ha; simp [p1652] at ha; subst a; trivial
  · exact checked1652
theorem derived1652 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1652 := by
  apply localUnsat_implies_entails f1652 [c1629, c1486, c1643, c37, c1648, c1650, c82, c50, c333, c53, c63, c286, c374, c355, c353, c43, c83, c62, c297, c1651, c21, c24, c226, c241, c265] c1652 unsat1652 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1648 := derived1648 a h
  have h5 : Entails.eval a c1650 := derived1650 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c374 := h 373 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c353 := h 352 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c83 := h 82 (by decide)
  have h17 : Entails.eval a c62 := h 61 (by decide)
  have h18 : Entails.eval a c297 := h 296 (by decide)
  have h19 : Entails.eval a c1651 := derived1651 a h
  have h20 : Entails.eval a c21 := h 20 (by decide)
  have h21 : Entails.eval a c24 := h 23 (by decide)
  have h22 : Entails.eval a c226 := h 225 (by decide)
  have h23 : Entails.eval a c241 := h 240 (by decide)
  have h24 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1653 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨7, by decide⟩, false), (⟨28, by decide⟩, true), (⟨39, by decide⟩, true), (⟨8, by decide⟩, false), (⟨36, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1653 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c149, some c160, some c16, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1653 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1653 : lratChecker f1653 p1653 = .success := by decide +kernel
theorem unsat1653 : Unsatisfiable (PosFin 57) f1653 := by
  apply lratCheckerSound f1653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1653
  · intro a ha; simp [p1653] at ha; subst a; trivial
  · exact checked1653
theorem derived1653 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1653 := by
  apply localUnsat_implies_entails f1653 [c149, c160, c16] c1653 unsat1653 (by rfl) a
  have h0 : Entails.eval a c149 := h 148 (by decide)
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1654 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1654 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c37, some c1650, some c82, some c50, some c33, some c87, some c314, some c286, some c344, some c387, some c51, some c53, some c508, some c75, some c349, some c297, some c369, some c68, some c1653, some c177, some c164, some c186, some c713, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1654 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1654 : lratChecker f1654 p1654 = .success := by decide +kernel
theorem unsat1654 : Unsatisfiable (PosFin 57) f1654 := by
  apply lratCheckerSound f1654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1654
  · intro a ha; simp [p1654] at ha; subst a; trivial
  · exact checked1654
theorem derived1654 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1654 := by
  apply localUnsat_implies_entails f1654 [c1486, c1629, c37, c1650, c82, c50, c33, c87, c314, c286, c344, c387, c51, c53, c508, c75, c349, c297, c369, c68, c1653, c177, c164, c186, c713] c1654 unsat1654 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c1650 := derived1650 a h
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c87 := h 86 (by decide)
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c286 := h 285 (by decide)
  have h10 : Entails.eval a c344 := h 343 (by decide)
  have h11 : Entails.eval a c387 := h 386 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c508 := derived508 a h
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  have h17 : Entails.eval a c297 := h 296 (by decide)
  have h18 : Entails.eval a c369 := h 368 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c1653 := derived1653 a h
  have h21 : Entails.eval a c177 := h 176 (by decide)
  have h22 : Entails.eval a c164 := h 163 (by decide)
  have h23 : Entails.eval a c186 := h 185 (by decide)
  have h24 : Entails.eval a c713 := derived713 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1655 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨29, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1655 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c37, some c1648, some c1650, some c82, some c50, some c1654, some c333, some c1652, some c53, some c317, some c286, some c43, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1655 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1655 : lratChecker f1655 p1655 = .success := by decide +kernel
theorem unsat1655 : Unsatisfiable (PosFin 57) f1655 := by
  apply lratCheckerSound f1655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1655
  · intro a ha; simp [p1655] at ha; subst a; trivial
  · exact checked1655
theorem derived1655 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1655 := by
  apply localUnsat_implies_entails f1655 [c1629, c1486, c37, c1648, c1650, c82, c50, c1654, c333, c1652, c53, c317, c286, c43] c1655 unsat1655 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c1648 := derived1648 a h
  have h4 : Entails.eval a c1650 := derived1650 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c1654 := derived1654 a h
  have h8 : Entails.eval a c333 := h 332 (by decide)
  have h9 : Entails.eval a c1652 := derived1652 a h
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c317 := h 316 (by decide)
  have h12 : Entails.eval a c286 := h 285 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1656 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1656 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c333, some c53, some c62, some c358, some c342, some c90, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1656 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1656 : lratChecker f1656 p1656 = .success := by decide +kernel
theorem unsat1656 : Unsatisfiable (PosFin 57) f1656 := by
  apply lratCheckerSound f1656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1656
  · intro a ha; simp [p1656] at ha; subst a; trivial
  · exact checked1656
theorem derived1656 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1656 := by
  apply localUnsat_implies_entails f1656 [c1486, c1629, c333, c53, c62, c358, c342, c90] c1656 unsat1656 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c62 := h 61 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c342 := h 341 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1657 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1657 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1486, some c1629, some c50, some c37, some c1648, some c1650, some c82, some c1655, some c100, some c1656, some c33, some c86, some c286, some c342, some c508, some c66, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1657 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1657 : lratChecker f1657 p1657 = .success := by decide +kernel
theorem unsat1657 : Unsatisfiable (PosFin 57) f1657 := by
  apply lratCheckerSound f1657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1657
  · intro a ha; simp [p1657] at ha; subst a; trivial
  · exact checked1657
theorem derived1657 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1657 := by
  apply localUnsat_implies_entails f1657 [c1643, c1486, c1629, c50, c37, c1648, c1650, c82, c1655, c100, c1656, c33, c86, c286, c342, c508, c66] c1657 unsat1657 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1648 := derived1648 a h
  have h6 : Entails.eval a c1650 := derived1650 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c1655 := derived1655 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c1656 := derived1656 a h
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c342 := h 341 (by decide)
  have h15 : Entails.eval a c508 := derived508 a h
  have h16 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1658 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨53, by decide⟩, false), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1658 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c70, some c353, some c57, some c1657, some c1630, some c56, some c36, some c368, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1658 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1658 : lratChecker f1658 p1658 = .success := by decide +kernel
theorem unsat1658 : Unsatisfiable (PosFin 57) f1658 := by
  apply lratCheckerSound f1658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1658
  · intro a ha; simp [p1658] at ha; subst a; trivial
  · exact checked1658
theorem derived1658 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1658 := by
  apply localUnsat_implies_entails f1658 [c1629, c70, c353, c57, c1657, c1630, c56, c36, c368] c1658 unsat1658 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c1657 := derived1657 a h
  have h5 : Entails.eval a c1630 := derived1630 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c368 := h 367 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1659 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨53, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1659 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c357, some c53, some c74, some c334, some c366, some c90, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true))]
def p1659 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1659 : lratChecker f1659 p1659 = .success := by decide +kernel
theorem unsat1659 : Unsatisfiable (PosFin 57) f1659 := by
  apply lratCheckerSound f1659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1659
  · intro a ha; simp [p1659] at ha; subst a; trivial
  · exact checked1659
theorem derived1659 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1659 := by
  apply localUnsat_implies_entails f1659 [c1486, c1629, c357, c53, c74, c334, c366, c90] c1659 unsat1659 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c74 := h 73 (by decide)
  have h5 : Entails.eval a c334 := h 333 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1660 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨53, by decide⟩, false), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1660 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1643, some c1486, some c1657, some c70, some c57, some c1658, some c100, some c1659, some c33, some c86, some c285, some c366, some c74, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1660 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1660 : lratChecker f1660 p1660 = .success := by decide +kernel
theorem unsat1660 : Unsatisfiable (PosFin 57) f1660 := by
  apply lratCheckerSound f1660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1660
  · intro a ha; simp [p1660] at ha; subst a; trivial
  · exact checked1660
theorem derived1660 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1660 := by
  apply localUnsat_implies_entails f1660 [c1629, c1643, c1486, c1657, c70, c57, c1658, c100, c1659, c33, c86, c285, c366, c74] c1660 unsat1660 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1643 := derived1643 a h
  have h2 : Entails.eval a c1486 := derived1486 a h
  have h3 : Entails.eval a c1657 := derived1657 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c1658 := derived1658 a h
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c1659 := derived1659 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c366 := h 365 (by decide)
  have h13 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1661 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1661 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c344, some c36, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1661 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1661 : lratChecker f1661 p1661 = .success := by decide +kernel
theorem unsat1661 : Unsatisfiable (PosFin 57) f1661 := by
  apply lratCheckerSound f1661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1661
  · intro a ha; simp [p1661] at ha; subst a; trivial
  · exact checked1661
theorem derived1661 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1661 := by
  apply localUnsat_implies_entails f1661 [c280, c344, c36] c1661 unsat1661 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1662 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1662 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c269, some c333, some c33, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1662 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1662 : lratChecker f1662 p1662 = .success := by decide +kernel
theorem unsat1662 : Unsatisfiable (PosFin 57) f1662 := by
  apply lratCheckerSound f1662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1662
  · intro a ha; simp [p1662] at ha; subst a; trivial
  · exact checked1662
theorem derived1662 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1662 := by
  apply localUnsat_implies_entails f1662 [c1486, c269, c333, c33] c1662 unsat1662 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1663 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1663 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1662, some c1661, some c63, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1663 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1663 : lratChecker f1663 p1663 = .success := by decide +kernel
theorem unsat1663 : Unsatisfiable (PosFin 57) f1663 := by
  apply lratCheckerSound f1663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1663
  · intro a ha; simp [p1663] at ha; subst a; trivial
  · exact checked1663
theorem derived1663 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1663 := by
  apply localUnsat_implies_entails f1663 [c1486, c1662, c1661, c63] c1663 unsat1663 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1662 := derived1662 a h
  have h2 : Entails.eval a c1661 := derived1661 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1664 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1664 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1643, some c1486, some c1657, some c1660, some c1636, some c82, some c1662, some c1663, some c100, some c1656, some c62, some c86, some c342, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1664 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1664 : lratChecker f1664 p1664 = .success := by decide +kernel
theorem unsat1664 : Unsatisfiable (PosFin 57) f1664 := by
  apply lratCheckerSound f1664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1664
  · intro a ha; simp [p1664] at ha; subst a; trivial
  · exact checked1664
theorem derived1664 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1664 := by
  apply localUnsat_implies_entails f1664 [c1629, c1643, c1486, c1657, c1660, c1636, c82, c1662, c1663, c100, c1656, c62, c86, c342] c1664 unsat1664 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1643 := derived1643 a h
  have h2 : Entails.eval a c1486 := derived1486 a h
  have h3 : Entails.eval a c1657 := derived1657 a h
  have h4 : Entails.eval a c1660 := derived1660 a h
  have h5 : Entails.eval a c1636 := derived1636 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c1662 := derived1662 a h
  have h8 : Entails.eval a c1663 := derived1663 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c1656 := derived1656 a h
  have h11 : Entails.eval a c62 := h 61 (by decide)
  have h12 : Entails.eval a c86 := h 85 (by decide)
  have h13 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1665 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, true), (⟨45, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1665 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c161, some c176, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1665 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1665 : lratChecker f1665 p1665 = .success := by decide +kernel
theorem unsat1665 : Unsatisfiable (PosFin 57) f1665 := by
  apply lratCheckerSound f1665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1665
  · intro a ha; simp [p1665] at ha; subst a; trivial
  · exact checked1665
theorem derived1665 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1665 := by
  apply localUnsat_implies_entails f1665 [c163, c161, c176] c1665 unsat1665 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c161 := h 160 (by decide)
  have h2 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1666 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1666 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1643, some c70, some c354, some c71, some c1664, some c94, some c339, some c353, some c57, some c1657, some c1630, some c63, some c56, some c43, some c334, some c270, some c313, some c1665, some c8, some c420, some c181, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1666 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1666 : lratChecker f1666 p1666 = .success := by decide +kernel
theorem unsat1666 : Unsatisfiable (PosFin 57) f1666 := by
  apply lratCheckerSound f1666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1666
  · intro a ha; simp [p1666] at ha; subst a; trivial
  · exact checked1666
theorem derived1666 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1666 := by
  apply localUnsat_implies_entails f1666 [c1629, c1486, c1643, c70, c354, c71, c1664, c94, c339, c353, c57, c1657, c1630, c63, c56, c43, c334, c270, c313, c1665, c8, c420, c181] c1666 unsat1666 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1664 := derived1664 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c339 := h 338 (by decide)
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c1657 := derived1657 a h
  have h12 : Entails.eval a c1630 := derived1630 a h
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c43 := h 42 (by decide)
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c313 := h 312 (by decide)
  have h19 : Entails.eval a c1665 := derived1665 a h
  have h20 : Entails.eval a c8 := h 7 (by decide)
  have h21 : Entails.eval a c420 := derived420 a h
  have h22 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1667 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨3, by decide⟩, true), (⟨45, by decide⟩, false), (⟨38, by decide⟩, false), (⟨54, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1667 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c334, some c53, some c285, some c358, some c42, some c78, some c294, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1667 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1667 : lratChecker f1667 p1667 = .success := by decide +kernel
theorem unsat1667 : Unsatisfiable (PosFin 57) f1667 := by
  apply lratCheckerSound f1667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1667
  · intro a ha; simp [p1667] at ha; subst a; trivial
  · exact checked1667
theorem derived1667 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1667 := by
  apply localUnsat_implies_entails f1667 [c1486, c1629, c334, c53, c285, c358, c42, c78, c294] c1667 unsat1667 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c334 := h 333 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c358 := h 357 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1668 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨45, by decide⟩, false), (⟨29, by decide⟩, false), (⟨38, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1668 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1667, some c33, some c285, some c508, some c74, some c46, some c294, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1668 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1668 : lratChecker f1668 p1668 = .success := by decide +kernel
theorem unsat1668 : Unsatisfiable (PosFin 57) f1668 := by
  apply lratCheckerSound f1668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1668
  · intro a ha; simp [p1668] at ha; subst a; trivial
  · exact checked1668
theorem derived1668 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1668 := by
  apply localUnsat_implies_entails f1668 [c1629, c1486, c1667, c33, c285, c508, c74, c46, c294] c1668 unsat1668 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1667 := derived1667 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c508 := derived508 a h
  have h6 : Entails.eval a c74 := h 73 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1669 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1669 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1643, some c1664, some c94, some c1657, some c70, some c57, some c1666, some c100, some c1668, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1669 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1669 : lratChecker f1669 p1669 = .success := by decide +kernel
theorem unsat1669 : Unsatisfiable (PosFin 57) f1669 := by
  apply lratCheckerSound f1669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1669
  · intro a ha; simp [p1669] at ha; subst a; trivial
  · exact checked1669
theorem derived1669 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1669 := by
  apply localUnsat_implies_entails f1669 [c1629, c1643, c1664, c94, c1657, c70, c57, c1666, c100, c1668] c1669 unsat1669 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1643 := derived1643 a h
  have h2 : Entails.eval a c1664 := derived1664 a h
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c1657 := derived1657 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c1666 := derived1666 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c1668 := derived1668 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1670 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨45, by decide⟩, false), (⟨4, by decide⟩, true), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1670 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c296, some c56, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1670 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1670 : lratChecker f1670 p1670 = .success := by decide +kernel
theorem unsat1670 : Unsatisfiable (PosFin 57) f1670 := by
  apply lratCheckerSound f1670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1670
  · intro a ha; simp [p1670] at ha; subst a; trivial
  · exact checked1670
theorem derived1670 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1670 := by
  apply localUnsat_implies_entails f1670 [c280, c296, c56] c1670 unsat1670 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c296 := h 295 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1671 : DefaultClause 57 := directClause [(⟨45, by decide⟩, false), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1671 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1670, some c43, some c269, some c285, some c53, some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1671 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1671 : lratChecker f1671 p1671 = .success := by decide +kernel
theorem unsat1671 : Unsatisfiable (PosFin 57) f1671 := by
  apply lratCheckerSound f1671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1671
  · intro a ha; simp [p1671] at ha; subst a; trivial
  · exact checked1671
theorem derived1671 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1671 := by
  apply localUnsat_implies_entails f1671 [c1486, c1670, c43, c269, c285, c53] c1671 unsat1671 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1670 := derived1670 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c285 := h 284 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1672 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1672 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1669, some c1657, some c1671, some c82, some c1664, some c94, some c269, some c349, some c33, some c43, some c382, some c358, some c334, some c319, some c1280, some c280, some c95, some c75, some c42, some c369, some c297, some c1511, some c177, some c146, some c164, some c11, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1672 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1672 : lratChecker f1672 p1672 = .success := by decide +kernel
theorem unsat1672 : Unsatisfiable (PosFin 57) f1672 := by
  apply lratCheckerSound f1672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1672
  · intro a ha; simp [p1672] at ha; subst a; trivial
  · exact checked1672
theorem derived1672 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1672 := by
  apply localUnsat_implies_entails f1672 [c1629, c1486, c1669, c1657, c1671, c82, c1664, c94, c269, c349, c33, c43, c382, c358, c334, c319, c1280, c280, c95, c75, c42, c369, c297, c1511, c177, c146, c164, c11] c1672 unsat1672 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1669 := derived1669 a h
  have h3 : Entails.eval a c1657 := derived1657 a h
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c1664 := derived1664 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c349 := h 348 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c382 := h 381 (by decide)
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c334 := h 333 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c1280 := derived1280 a h
  have h17 : Entails.eval a c280 := h 279 (by decide)
  have h18 : Entails.eval a c95 := h 94 (by decide)
  have h19 : Entails.eval a c75 := h 74 (by decide)
  have h20 : Entails.eval a c42 := h 41 (by decide)
  have h21 : Entails.eval a c369 := h 368 (by decide)
  have h22 : Entails.eval a c297 := h 296 (by decide)
  have h23 : Entails.eval a c1511 := derived1511 a h
  have h24 : Entails.eval a c177 := h 176 (by decide)
  have h25 : Entails.eval a c146 := h 145 (by decide)
  have h26 : Entails.eval a c164 := h 163 (by decide)
  have h27 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1673 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨30, by decide⟩, true), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, true), (⟨46, by decide⟩, false), (⟨37, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1673 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c53, some c479, some c154, some c166, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1673 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1673 : lratChecker f1673 p1673 = .success := by decide +kernel
theorem unsat1673 : Unsatisfiable (PosFin 57) f1673 := by
  apply lratCheckerSound f1673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1673
  · intro a ha; simp [p1673] at ha; subst a; trivial
  · exact checked1673
theorem derived1673 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1673 := by
  apply localUnsat_implies_entails f1673 [c1486, c53, c479, c154, c166] c1673 unsat1673 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c53 := h 52 (by decide)
  have h2 : Entails.eval a c479 := derived479 a h
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1674 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1674 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1643, some c1669, some c1664, some c94, some c1657, some c1671, some c82, some c1672, some c53, some c63, some c1503, some c358, some c280, some c355, some c353, some c33, some c1596, some c62, some c313, some c286, some c1673, some c11, some c5, some c152, some c181, some c166, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1674 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1674 : lratChecker f1674 p1674 = .success := by decide +kernel
theorem unsat1674 : Unsatisfiable (PosFin 57) f1674 := by
  apply lratCheckerSound f1674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1674
  · intro a ha; simp [p1674] at ha; subst a; trivial
  · exact checked1674
theorem derived1674 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1674 := by
  apply localUnsat_implies_entails f1674 [c1629, c1486, c1643, c1669, c1664, c94, c1657, c1671, c82, c1672, c53, c63, c1503, c358, c280, c355, c353, c33, c1596, c62, c313, c286, c1673, c11, c5, c152, c181, c166] c1674 unsat1674 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c1669 := derived1669 a h
  have h4 : Entails.eval a c1664 := derived1664 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c1657 := derived1657 a h
  have h7 : Entails.eval a c1671 := derived1671 a h
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c1672 := derived1672 a h
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c1503 := derived1503 a h
  have h13 : Entails.eval a c358 := h 357 (by decide)
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c355 := h 354 (by decide)
  have h16 : Entails.eval a c353 := h 352 (by decide)
  have h17 : Entails.eval a c33 := h 32 (by decide)
  have h18 : Entails.eval a c1596 := derived1596 a h
  have h19 : Entails.eval a c62 := h 61 (by decide)
  have h20 : Entails.eval a c313 := h 312 (by decide)
  have h21 : Entails.eval a c286 := h 285 (by decide)
  have h22 : Entails.eval a c1673 := derived1673 a h
  have h23 : Entails.eval a c11 := h 10 (by decide)
  have h24 : Entails.eval a c5 := h 4 (by decide)
  have h25 : Entails.eval a c152 := h 151 (by decide)
  have h26 : Entails.eval a c181 := h 180 (by decide)
  have h27 : Entails.eval a c166 := h 165 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1675 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1675 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1486, some c1629, some c1674, some c100, some c1669, some c1657, some c58, some c723, some c42, some c46, some c1638, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1675 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1675 : lratChecker f1675 p1675 = .success := by decide +kernel
theorem unsat1675 : Unsatisfiable (PosFin 57) f1675 := by
  apply lratCheckerSound f1675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1675
  · intro a ha; simp [p1675] at ha; subst a; trivial
  · exact checked1675
theorem derived1675 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1675 := by
  apply localUnsat_implies_entails f1675 [c1643, c1486, c1629, c1674, c100, c1669, c1657, c58, c723, c42, c46, c1638] c1675 unsat1675 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c1674 := derived1674 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c1669 := derived1669 a h
  have h6 : Entails.eval a c1657 := derived1657 a h
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c723 := derived723 a h
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c1638 := derived1638 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1676 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨46, by decide⟩, false), (⟨38, by decide⟩, false), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1676 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c358, some c334, some c53, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p1676 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1676 : lratChecker f1676 p1676 = .success := by decide +kernel
theorem unsat1676 : Unsatisfiable (PosFin 57) f1676 := by
  apply lratCheckerSound f1676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1676
  · intro a ha; simp [p1676] at ha; subst a; trivial
  · exact checked1676
theorem derived1676 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1676 := by
  apply localUnsat_implies_entails f1676 [c1486, c358, c334, c53] c1676 unsat1676 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c358 := h 357 (by decide)
  have h2 : Entails.eval a c334 := h 333 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1677 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1677 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1643, some c1657, some c1664, some c94, some c1669, some c1674, some c100, some c1675, some c1668, some c82, some c1676, some c33, some c269, some c1638, some c62, some c46, some c278, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1677 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1677 : lratChecker f1677 p1677 = .success := by decide +kernel
theorem unsat1677 : Unsatisfiable (PosFin 57) f1677 := by
  apply lratCheckerSound f1677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1677
  · intro a ha; simp [p1677] at ha; subst a; trivial
  · exact checked1677
theorem derived1677 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1677 := by
  apply localUnsat_implies_entails f1677 [c1629, c1486, c1643, c1657, c1664, c94, c1669, c1674, c100, c1675, c1668, c82, c1676, c33, c269, c1638, c62, c46, c278] c1677 unsat1677 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c1657 := derived1657 a h
  have h4 : Entails.eval a c1664 := derived1664 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c1669 := derived1669 a h
  have h7 : Entails.eval a c1674 := derived1674 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c1675 := derived1675 a h
  have h10 : Entails.eval a c1668 := derived1668 a h
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c1676 := derived1676 a h
  have h13 : Entails.eval a c33 := h 32 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c1638 := derived1638 a h
  have h16 : Entails.eval a c62 := h 61 (by decide)
  have h17 : Entails.eval a c46 := h 45 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1678 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1678 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c57, some c70, some c37, some c50, some c33, some c43, some c357, some c281, some c317, some c53, some c350, some c71, some c1645, some c1647, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1678 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1678 : lratChecker f1678 p1678 = .success := by decide +kernel
theorem unsat1678 : Unsatisfiable (PosFin 57) f1678 := by
  apply lratCheckerSound f1678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1678
  · intro a ha; simp [p1678] at ha; subst a; trivial
  · exact checked1678
theorem derived1678 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1678 := by
  apply localUnsat_implies_entails f1678 [c1629, c1486, c57, c70, c37, c50, c33, c43, c357, c281, c317, c53, c350, c71, c1645, c1647] c1678 unsat1678 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c357 := h 356 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c317 := h 316 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c350 := h 349 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  have h14 : Entails.eval a c1645 := derived1645 a h
  have h15 : Entails.eval a c1647 := derived1647 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1679 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨3, by decide⟩, false), (⟨54, by decide⟩, true), (⟨51, by decide⟩, true), (⟨28, by decide⟩, true), (⟨8, by decide⟩, false), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1679 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c5, some c8, some c186, some c149, some c197, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1679 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1679 : lratChecker f1679 p1679 = .success := by decide +kernel
theorem unsat1679 : Unsatisfiable (PosFin 57) f1679 := by
  apply lratCheckerSound f1679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1679
  · intro a ha; simp [p1679] at ha; subst a; trivial
  · exact checked1679
theorem derived1679 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1679 := by
  apply localUnsat_implies_entails f1679 [c1643, c5, c8, c186, c149, c197] c1679 unsat1679 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c149 := h 148 (by decide)
  have h5 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1680 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1680 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c57, some c70, some c37, some c50, some c1677, some c1678, some c270, some c314, some c53, some c63, some c51, some c357, some c281, some c87, some c387, some c345, some c86, some c1679, some c153, some c156, some c165, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1680 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1680 : lratChecker f1680 p1680 = .success := by decide +kernel
theorem unsat1680 : Unsatisfiable (PosFin 57) f1680 := by
  apply lratCheckerSound f1680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1680
  · intro a ha; simp [p1680] at ha; subst a; trivial
  · exact checked1680
theorem derived1680 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1680 := by
  apply localUnsat_implies_entails f1680 [c1629, c1486, c57, c70, c37, c50, c1677, c1678, c270, c314, c53, c63, c51, c357, c281, c87, c387, c345, c86, c1679, c153, c156, c165] c1680 unsat1680 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c1677 := derived1677 a h
  have h7 : Entails.eval a c1678 := derived1678 a h
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c314 := h 313 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c357 := h 356 (by decide)
  have h14 : Entails.eval a c281 := h 280 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  have h16 : Entails.eval a c387 := h 386 (by decide)
  have h17 : Entails.eval a c345 := h 344 (by decide)
  have h18 : Entails.eval a c86 := h 85 (by decide)
  have h19 : Entails.eval a c1679 := derived1679 a h
  have h20 : Entails.eval a c153 := h 152 (by decide)
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1681 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1681 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1486, some c1629, some c37, some c50, some c70, some c57, some c1680, some c100, some c1659, some c86, some c33, some c508, some c366, some c286, some c78, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1681 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1681 : lratChecker f1681 p1681 = .success := by decide +kernel
theorem unsat1681 : Unsatisfiable (PosFin 57) f1681 := by
  apply lratCheckerSound f1681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1681
  · intro a ha; simp [p1681] at ha; subst a; trivial
  · exact checked1681
theorem derived1681 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1681 := by
  apply localUnsat_implies_entails f1681 [c1643, c1486, c1629, c37, c50, c70, c57, c1680, c100, c1659, c86, c33, c508, c366, c286, c78] c1681 unsat1681 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1629 := derived1629 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c1680 := derived1680 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c1659 := derived1659 a h
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c508 := derived508 a h
  have h13 : Entails.eval a c366 := h 365 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  have h15 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1682 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1682 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1643, some c37, some c1681, some c1650, some c82, some c50, some c1654, some c333, some c1656, some c53, some c63, some c286, some c374, some c355, some c43, some c83, some c281, some c317, some c297, some c1651, some c21, some c24, some c226, some c241, some c265, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1682 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1682 : lratChecker f1682 p1682 = .success := by decide +kernel
theorem unsat1682 : Unsatisfiable (PosFin 57) f1682 := by
  apply lratCheckerSound f1682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1682
  · intro a ha; simp [p1682] at ha; subst a; trivial
  · exact checked1682
theorem derived1682 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1682 := by
  apply localUnsat_implies_entails f1682 [c1629, c1486, c1643, c37, c1681, c1650, c82, c50, c1654, c333, c1656, c53, c63, c286, c374, c355, c43, c83, c281, c317, c297, c1651, c21, c24, c226, c241, c265] c1682 unsat1682 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c1681 := derived1681 a h
  have h5 : Entails.eval a c1650 := derived1650 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c1654 := derived1654 a h
  have h9 : Entails.eval a c333 := h 332 (by decide)
  have h10 : Entails.eval a c1656 := derived1656 a h
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c63 := h 62 (by decide)
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c374 := h 373 (by decide)
  have h15 : Entails.eval a c355 := h 354 (by decide)
  have h16 : Entails.eval a c43 := h 42 (by decide)
  have h17 : Entails.eval a c83 := h 82 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c317 := h 316 (by decide)
  have h20 : Entails.eval a c297 := h 296 (by decide)
  have h21 : Entails.eval a c1651 := derived1651 a h
  have h22 : Entails.eval a c21 := h 20 (by decide)
  have h23 : Entails.eval a c24 := h 23 (by decide)
  have h24 : Entails.eval a c226 := h 225 (by decide)
  have h25 : Entails.eval a c241 := h 240 (by decide)
  have h26 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1683 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1683 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c1643, some c50, some c37, some c1681, some c1650, some c82, some c1682, some c100, some c1656, some c86, some c33, some c342, some c286, some c66, some c508, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1683 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1683 : lratChecker f1683 p1683 = .success := by decide +kernel
theorem unsat1683 : Unsatisfiable (PosFin 57) f1683 := by
  apply lratCheckerSound f1683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1683
  · intro a ha; simp [p1683] at ha; subst a; trivial
  · exact checked1683
theorem derived1683 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1683 := by
  apply localUnsat_implies_entails f1683 [c1486, c1629, c1643, c50, c37, c1681, c1650, c82, c1682, c100, c1656, c86, c33, c342, c286, c66, c508] c1683 unsat1683 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c1681 := derived1681 a h
  have h6 : Entails.eval a c1650 := derived1650 a h
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c1682 := derived1682 a h
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c1656 := derived1656 a h
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c342 := h 341 (by decide)
  have h14 : Entails.eval a c286 := h 285 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c508 := derived508 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1684 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨52, by decide⟩, true), (⟨56, by decide⟩, true), (⟨30, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1684 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c5, some c1175, some c146, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1684 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1684 : lratChecker f1684 p1684 = .success := by decide +kernel
theorem unsat1684 : Unsatisfiable (PosFin 57) f1684 := by
  apply lratCheckerSound f1684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1684
  · intro a ha; simp [p1684] at ha; subst a; trivial
  · exact checked1684
theorem derived1684 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1684 := by
  apply localUnsat_implies_entails f1684 [c1643, c5, c1175, c146] c1684 unsat1684 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c1175 := derived1175 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1685 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1685 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c57, some c70, some c1683, some c1677, some c33, some c43, some c319, some c296, some c42, some c56, some c75, some c281, some c357, some c38, some c382, some c334, some c345, some c1684, some c153, some c1278, some c165, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1685 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1685 : lratChecker f1685 p1685 = .success := by decide +kernel
theorem unsat1685 : Unsatisfiable (PosFin 57) f1685 := by
  apply lratCheckerSound f1685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1685
  · intro a ha; simp [p1685] at ha; subst a; trivial
  · exact checked1685
theorem derived1685 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1685 := by
  apply localUnsat_implies_entails f1685 [c1486, c1629, c57, c70, c1683, c1677, c33, c43, c319, c296, c42, c56, c75, c281, c357, c38, c382, c334, c345, c1684, c153, c1278, c165] c1685 unsat1685 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c1683 := derived1683 a h
  have h5 : Entails.eval a c1677 := derived1677 a h
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c43 := h 42 (by decide)
  have h8 : Entails.eval a c319 := h 318 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c56 := h 55 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c357 := h 356 (by decide)
  have h15 : Entails.eval a c38 := h 37 (by decide)
  have h16 : Entails.eval a c382 := h 381 (by decide)
  have h17 : Entails.eval a c334 := h 333 (by decide)
  have h18 : Entails.eval a c345 := h 344 (by decide)
  have h19 : Entails.eval a c1684 := derived1684 a h
  have h20 : Entails.eval a c153 := h 152 (by decide)
  have h21 : Entails.eval a c1278 := derived1278 a h
  have h22 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1686 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨37, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1686 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1486, some c1629, some c1643, some c57, some c70, some c1683, some c1685, some c313, some c285, some c53, some c75, some c270, some c350, some c296, some c38, some c71, some c36, some c334, some c385, some c345, some c1665, some c8, some c420, some c181, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1686 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1686 : lratChecker f1686 p1686 = .success := by decide +kernel
theorem unsat1686 : Unsatisfiable (PosFin 57) f1686 := by
  apply lratCheckerSound f1686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1686
  · intro a ha; simp [p1686] at ha; subst a; trivial
  · exact checked1686
theorem derived1686 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1686 := by
  apply localUnsat_implies_entails f1686 [c1486, c1629, c1643, c57, c70, c1683, c1685, c313, c285, c53, c75, c270, c350, c296, c38, c71, c36, c334, c385, c345, c1665, c8, c420, c181] c1686 unsat1686 (by rfl) a
  have h0 : Entails.eval a c1486 := derived1486 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1643 := derived1643 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c1683 := derived1683 a h
  have h6 : Entails.eval a c1685 := derived1685 a h
  have h7 : Entails.eval a c313 := h 312 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c75 := h 74 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c350 := h 349 (by decide)
  have h13 : Entails.eval a c296 := h 295 (by decide)
  have h14 : Entails.eval a c38 := h 37 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c36 := h 35 (by decide)
  have h17 : Entails.eval a c334 := h 333 (by decide)
  have h18 : Entails.eval a c385 := h 384 (by decide)
  have h19 : Entails.eval a c345 := h 344 (by decide)
  have h20 : Entails.eval a c1665 := derived1665 a h
  have h21 : Entails.eval a c8 := h 7 (by decide)
  have h22 : Entails.eval a c420 := derived420 a h
  have h23 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1687 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1687 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1643, some c1629, some c1486, some c1683, some c70, some c57, some c1686, some c100, some c1668, some c38, some c94, some c1659, some c33, some c508, some c285, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1687 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1687 : lratChecker f1687 p1687 = .success := by decide +kernel
theorem unsat1687 : Unsatisfiable (PosFin 57) f1687 := by
  apply lratCheckerSound f1687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1687
  · intro a ha; simp [p1687] at ha; subst a; trivial
  · exact checked1687
theorem derived1687 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1687 := by
  apply localUnsat_implies_entails f1687 [c1643, c1629, c1486, c1683, c70, c57, c1686, c100, c1668, c38, c94, c1659, c33, c508, c285] c1687 unsat1687 (by rfl) a
  have h0 : Entails.eval a c1643 := derived1643 a h
  have h1 : Entails.eval a c1629 := derived1629 a h
  have h2 : Entails.eval a c1486 := derived1486 a h
  have h3 : Entails.eval a c1683 := derived1683 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c1686 := derived1686 a h
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c1668 := derived1668 a h
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c1659 := derived1659 a h
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c508 := derived508 a h
  have h14 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1688 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1688 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1629, some c1486, some c1687, some c1683, some c1671, some c82, some c1663, some c94, some c1677, some c33, some c43, some c382, some c358, some c319, some c1280, some c280, some c95, some c53, some c75, some c42, some c349, some c297, some c369, some c1511, some c1684, some c177, some c157, some c146, some c11, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1688 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1688 : lratChecker f1688 p1688 = .success := by decide +kernel
theorem unsat1688 : Unsatisfiable (PosFin 57) f1688 := by
  apply lratCheckerSound f1688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1688
  · intro a ha; simp [p1688] at ha; subst a; trivial
  · exact checked1688
theorem derived1688 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1688 := by
  apply localUnsat_implies_entails f1688 [c1629, c1486, c1687, c1683, c1671, c82, c1663, c94, c1677, c33, c43, c382, c358, c319, c1280, c280, c95, c53, c75, c42, c349, c297, c369, c1511, c1684, c177, c157, c146, c11] c1688 unsat1688 (by rfl) a
  have h0 : Entails.eval a c1629 := derived1629 a h
  have h1 : Entails.eval a c1486 := derived1486 a h
  have h2 : Entails.eval a c1687 := derived1687 a h
  have h3 : Entails.eval a c1683 := derived1683 a h
  have h4 : Entails.eval a c1671 := derived1671 a h
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c1663 := derived1663 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c1677 := derived1677 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c382 := h 381 (by decide)
  have h12 : Entails.eval a c358 := h 357 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c1280 := derived1280 a h
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c95 := h 94 (by decide)
  have h17 : Entails.eval a c53 := h 52 (by decide)
  have h18 : Entails.eval a c75 := h 74 (by decide)
  have h19 : Entails.eval a c42 := h 41 (by decide)
  have h20 : Entails.eval a c349 := h 348 (by decide)
  have h21 : Entails.eval a c297 := h 296 (by decide)
  have h22 : Entails.eval a c369 := h 368 (by decide)
  have h23 : Entails.eval a c1511 := derived1511 a h
  have h24 : Entails.eval a c1684 := derived1684 a h
  have h25 : Entails.eval a c177 := h 176 (by decide)
  have h26 : Entails.eval a c157 := h 156 (by decide)
  have h27 : Entails.eval a c146 := h 145 (by decide)
  have h28 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1688

end CochromaticTwenty.Certificates.B16_7_2
