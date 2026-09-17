import MerLeanExperiment.Certificates.FixedCore0.Steps2000_2099

/-! Generated from the actual pinned fixed_core0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.FixedCore0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c9651 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9651 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9649, some c9498, some c9504, some c9506, some c9650, some c9648, some c9389, some c2140, some c9505, some c1235, some c3039, some c3578, some c2596, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9651 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9651 : lratChecker f9651 p9651 = .success := by decide +kernel
theorem unsat9651 : Unsatisfiable (PosFin 65) f9651 := by
  apply lratCheckerSound f9651 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9651
  · intro a ha; simp [p9651] at ha; subst a; trivial
  · exact checked9651
theorem derived9651 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9651 := by
  apply localUnsat_implies_entails f9651 [c9627, c9347, c9649, c9498, c9504, c9506, c9650, c9648, c9389, c2140, c9505, c1235, c3039, c3578, c2596] c9651 unsat9651 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9649 := derived9649 a h
  have h3 : Entails.eval a c9498 := derived9498 a h
  have h4 : Entails.eval a c9504 := derived9504 a h
  have h5 : Entails.eval a c9506 := derived9506 a h
  have h6 : Entails.eval a c9650 := derived9650 a h
  have h7 : Entails.eval a c9648 := derived9648 a h
  have h8 : Entails.eval a c9389 := derived9389 a h
  have h9 : Entails.eval a c2140 := h 2139 (by decide)
  have h10 : Entails.eval a c9505 := derived9505 a h
  have h11 : Entails.eval a c1235 := h 1234 (by decide)
  have h12 : Entails.eval a c3039 := h 3038 (by decide)
  have h13 : Entails.eval a c3578 := h 3577 (by decide)
  have h14 : Entails.eval a c2596 := h 2595 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9652 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9652 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9129, some c9629, some c9356, some c2098, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9652 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9652 : lratChecker f9652 p9652 = .success := by decide +kernel
theorem unsat9652 : Unsatisfiable (PosFin 65) f9652 := by
  apply lratCheckerSound f9652 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9652
  · intro a ha; simp [p9652] at ha; subst a; trivial
  · exact checked9652
theorem derived9652 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9652 := by
  apply localUnsat_implies_entails f9652 [c9627, c9347, c9129, c9629, c9356, c2098] c9652 unsat9652 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9129 := derived9129 a h
  have h3 : Entails.eval a c9629 := derived9629 a h
  have h4 : Entails.eval a c9356 := derived9356 a h
  have h5 : Entails.eval a c2098 := h 2097 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9653 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9653 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2148, some c2133, some c1218, some c1215, some c2141, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9653 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9653 : lratChecker f9653 p9653 = .success := by decide +kernel
theorem unsat9653 : Unsatisfiable (PosFin 65) f9653 := by
  apply lratCheckerSound f9653 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9653
  · intro a ha; simp [p9653] at ha; subst a; trivial
  · exact checked9653
theorem derived9653 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9653 := by
  apply localUnsat_implies_entails f9653 [c9627, c2148, c2133, c1218, c1215, c2141] c9653 unsat9653 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2148 := h 2147 (by decide)
  have h2 : Entails.eval a c2133 := h 2132 (by decide)
  have h3 : Entails.eval a c1218 := h 1217 (by decide)
  have h4 : Entails.eval a c1215 := h 1214 (by decide)
  have h5 : Entails.eval a c2141 := h 2140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9654 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨54, by decide⟩, false), (⟨53, by decide⟩, false), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9654 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2113, some c2102, some c2097, some c9145, some c4395, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9654 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9654 : lratChecker f9654 p9654 = .success := by decide +kernel
theorem unsat9654 : Unsatisfiable (PosFin 65) f9654 := by
  apply lratCheckerSound f9654 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9654
  · intro a ha; simp [p9654] at ha; subst a; trivial
  · exact checked9654
theorem derived9654 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9654 := by
  apply localUnsat_implies_entails f9654 [c9627, c2113, c2102, c2097, c9145, c4395] c9654 unsat9654 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2113 := h 2112 (by decide)
  have h2 : Entails.eval a c2102 := h 2101 (by decide)
  have h3 : Entails.eval a c2097 := h 2096 (by decide)
  have h4 : Entails.eval a c9145 := derived9145 a h
  have h5 : Entails.eval a c4395 := h 4394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9655 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9655 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9652, some c9651, some c9627, some c9347, some c9653, some c9654, some c9477, some c2861, some c8007, some c3480, some c3525, some c2851, some c3867, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9655 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9655 : lratChecker f9655 p9655 = .success := by decide +kernel
theorem unsat9655 : Unsatisfiable (PosFin 65) f9655 := by
  apply lratCheckerSound f9655 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9655
  · intro a ha; simp [p9655] at ha; subst a; trivial
  · exact checked9655
theorem derived9655 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9655 := by
  apply localUnsat_implies_entails f9655 [c9652, c9651, c9627, c9347, c9653, c9654, c9477, c2861, c8007, c3480, c3525, c2851, c3867] c9655 unsat9655 (by rfl) a
  have h0 : Entails.eval a c9652 := derived9652 a h
  have h1 : Entails.eval a c9651 := derived9651 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9653 := derived9653 a h
  have h5 : Entails.eval a c9654 := derived9654 a h
  have h6 : Entails.eval a c9477 := derived9477 a h
  have h7 : Entails.eval a c2861 := h 2860 (by decide)
  have h8 : Entails.eval a c8007 := derived8007 a h
  have h9 : Entails.eval a c3480 := h 3479 (by decide)
  have h10 : Entails.eval a c3525 := h 3524 (by decide)
  have h11 : Entails.eval a c2851 := h 2850 (by decide)
  have h12 : Entails.eval a c3867 := h 3866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9656 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9656 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9651, some c9627, some c9347, some c2140, some c1235, some c2528, some c4118, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9656 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9656 : lratChecker f9656 p9656 = .success := by decide +kernel
theorem unsat9656 : Unsatisfiable (PosFin 65) f9656 := by
  apply lratCheckerSound f9656 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9656
  · intro a ha; simp [p9656] at ha; subst a; trivial
  · exact checked9656
theorem derived9656 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9656 := by
  apply localUnsat_implies_entails f9656 [c9651, c9627, c9347, c2140, c1235, c2528, c4118] c9656 unsat9656 (by rfl) a
  have h0 : Entails.eval a c9651 := derived9651 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2140 := h 2139 (by decide)
  have h4 : Entails.eval a c1235 := h 1234 (by decide)
  have h5 : Entails.eval a c2528 := h 2527 (by decide)
  have h6 : Entails.eval a c4118 := h 4117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9657 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9657 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2105, some c2116, some c5027, some c2545, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9657 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9657 : lratChecker f9657 p9657 = .success := by decide +kernel
theorem unsat9657 : Unsatisfiable (PosFin 65) f9657 := by
  apply lratCheckerSound f9657 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9657
  · intro a ha; simp [p9657] at ha; subst a; trivial
  · exact checked9657
theorem derived9657 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9657 := by
  apply localUnsat_implies_entails f9657 [c9627, c9347, c2105, c2116, c5027, c2545] c9657 unsat9657 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2105 := h 2104 (by decide)
  have h3 : Entails.eval a c2116 := h 2115 (by decide)
  have h4 : Entails.eval a c5027 := h 5026 (by decide)
  have h5 : Entails.eval a c2545 := h 2544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9658 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9658 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9651, some c9347, some c9656, some c9657, some c2846, some c2866, some c2838, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9658 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9658 : lratChecker f9658 p9658 = .success := by decide +kernel
theorem unsat9658 : Unsatisfiable (PosFin 65) f9658 := by
  apply lratCheckerSound f9658 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9658
  · intro a ha; simp [p9658] at ha; subst a; trivial
  · exact checked9658
theorem derived9658 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9658 := by
  apply localUnsat_implies_entails f9658 [c9651, c9347, c9656, c9657, c2846, c2866, c2838] c9658 unsat9658 (by rfl) a
  have h0 : Entails.eval a c9651 := derived9651 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9656 := derived9656 a h
  have h3 : Entails.eval a c9657 := derived9657 a h
  have h4 : Entails.eval a c2846 := h 2845 (by decide)
  have h5 : Entails.eval a c2866 := h 2865 (by decide)
  have h6 : Entails.eval a c2838 := h 2837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9659 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨27, by decide⟩, false), (⟨1, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9659 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c630, some c8818, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p9659 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9659 : lratChecker f9659 p9659 = .success := by decide +kernel
theorem unsat9659 : Unsatisfiable (PosFin 65) f9659 := by
  apply lratCheckerSound f9659 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9659
  · intro a ha; simp [p9659] at ha; subst a; trivial
  · exact checked9659
theorem derived9659 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9659 := by
  apply localUnsat_implies_entails f9659 [c630, c8818] c9659 unsat9659 (by rfl) a
  have h0 : Entails.eval a c630 := h 629 (by decide)
  have h1 : Entails.eval a c8818 := derived8818 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9660 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9660 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9658, some c9651, some c9627, some c2135, some c9381, some c9154, some c9152, some c1229, some c1228, some c1237, some c2145, some c1238, some c9115, some c9557, some c9659, some c2129, some c2119, some c2122, some c2123, some c2127, some c2131, some c2118, some c9552, some c2132, some c1174, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9660 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked9660 : lratChecker f9660 p9660 = .success := by decide +kernel
theorem unsat9660 : Unsatisfiable (PosFin 65) f9660 := by
  apply lratCheckerSound f9660 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9660
  · intro a ha; simp [p9660] at ha; subst a; trivial
  · exact checked9660
theorem derived9660 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9660 := by
  apply localUnsat_implies_entails f9660 [c9658, c9651, c9627, c2135, c9381, c9154, c9152, c1229, c1228, c1237, c2145, c1238, c9115, c9557, c9659, c2129, c2119, c2122, c2123, c2127, c2131, c2118, c9552, c2132, c1174] c9660 unsat9660 (by rfl) a
  have h0 : Entails.eval a c9658 := derived9658 a h
  have h1 : Entails.eval a c9651 := derived9651 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c2135 := h 2134 (by decide)
  have h4 : Entails.eval a c9381 := derived9381 a h
  have h5 : Entails.eval a c9154 := derived9154 a h
  have h6 : Entails.eval a c9152 := derived9152 a h
  have h7 : Entails.eval a c1229 := h 1228 (by decide)
  have h8 : Entails.eval a c1228 := h 1227 (by decide)
  have h9 : Entails.eval a c1237 := h 1236 (by decide)
  have h10 : Entails.eval a c2145 := h 2144 (by decide)
  have h11 : Entails.eval a c1238 := h 1237 (by decide)
  have h12 : Entails.eval a c9115 := derived9115 a h
  have h13 : Entails.eval a c9557 := derived9557 a h
  have h14 : Entails.eval a c9659 := derived9659 a h
  have h15 : Entails.eval a c2129 := h 2128 (by decide)
  have h16 : Entails.eval a c2119 := h 2118 (by decide)
  have h17 : Entails.eval a c2122 := h 2121 (by decide)
  have h18 : Entails.eval a c2123 := h 2122 (by decide)
  have h19 : Entails.eval a c2127 := h 2126 (by decide)
  have h20 : Entails.eval a c2131 := h 2130 (by decide)
  have h21 : Entails.eval a c2118 := h 2117 (by decide)
  have h22 : Entails.eval a c9552 := derived9552 a h
  have h23 : Entails.eval a c2132 := h 2131 (by decide)
  have h24 : Entails.eval a c1174 := h 1173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9661 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨53, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9661 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2114, some c2100, some c4388, some c2108, some c9102, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9661 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9661 : lratChecker f9661 p9661 = .success := by decide +kernel
theorem unsat9661 : Unsatisfiable (PosFin 65) f9661 := by
  apply lratCheckerSound f9661 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9661
  · intro a ha; simp [p9661] at ha; subst a; trivial
  · exact checked9661
theorem derived9661 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9661 := by
  apply localUnsat_implies_entails f9661 [c9627, c2114, c2100, c4388, c2108, c9102] c9661 unsat9661 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2114 := h 2113 (by decide)
  have h2 : Entails.eval a c2100 := h 2099 (by decide)
  have h3 : Entails.eval a c4388 := h 4387 (by decide)
  have h4 : Entails.eval a c2108 := h 2107 (by decide)
  have h5 : Entails.eval a c9102 := derived9102 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9662 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨54, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9662 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9661, some c2864, some c9356, some c2838, some c2851, some c2867, some c2871, some c9102, some c2870, some c3866, some c3473, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9662 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9662 : lratChecker f9662 p9662 = .success := by decide +kernel
theorem unsat9662 : Unsatisfiable (PosFin 65) f9662 := by
  apply lratCheckerSound f9662 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9662
  · intro a ha; simp [p9662] at ha; subst a; trivial
  · exact checked9662
theorem derived9662 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9662 := by
  apply localUnsat_implies_entails f9662 [c9627, c9347, c9661, c2864, c9356, c2838, c2851, c2867, c2871, c9102, c2870, c3866, c3473] c9662 unsat9662 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9661 := derived9661 a h
  have h3 : Entails.eval a c2864 := h 2863 (by decide)
  have h4 : Entails.eval a c9356 := derived9356 a h
  have h5 : Entails.eval a c2838 := h 2837 (by decide)
  have h6 : Entails.eval a c2851 := h 2850 (by decide)
  have h7 : Entails.eval a c2867 := h 2866 (by decide)
  have h8 : Entails.eval a c2871 := h 2870 (by decide)
  have h9 : Entails.eval a c9102 := derived9102 a h
  have h10 : Entails.eval a c2870 := h 2869 (by decide)
  have h11 : Entails.eval a c3866 := h 3865 (by decide)
  have h12 : Entails.eval a c3473 := h 3472 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9663 : DefaultClause 65 := directClause [(⟨60, by decide⟩, false), (⟨51, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, false), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9663 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c5025, some c2545, some (DefaultClause.unit (⟨60, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9663 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9663 : lratChecker f9663 p9663 = .success := by decide +kernel
theorem unsat9663 : Unsatisfiable (PosFin 65) f9663 := by
  apply lratCheckerSound f9663 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9663
  · intro a ha; simp [p9663] at ha; subst a; trivial
  · exact checked9663
theorem derived9663 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9663 := by
  apply localUnsat_implies_entails f9663 [c9627, c9347, c5025, c2545] c9663 unsat9663 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c5025 := h 5024 (by decide)
  have h3 : Entails.eval a c2545 := h 2544 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9664 : DefaultClause 65 := directClause [(⟨57, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9664 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4716, some c3516, some c4288, some (DefaultClause.unit (⟨57, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9664 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9664 : lratChecker f9664 p9664 = .success := by decide +kernel
theorem unsat9664 : Unsatisfiable (PosFin 65) f9664 := by
  apply lratCheckerSound f9664 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9664
  · intro a ha; simp [p9664] at ha; subst a; trivial
  · exact checked9664
theorem derived9664 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9664 := by
  apply localUnsat_implies_entails f9664 [c4716, c3516, c4288] c9664 unsat9664 (by rfl) a
  have h0 : Entails.eval a c4716 := h 4715 (by decide)
  have h1 : Entails.eval a c3516 := h 3515 (by decide)
  have h2 : Entails.eval a c4288 := h 4287 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9665 : DefaultClause 65 := directClause [(⟨56, by decide⟩, true), (⟨57, by decide⟩, true), (⟨63, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9665 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3489, some c2892, some c3096, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨57, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9665 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9665 : lratChecker f9665 p9665 = .success := by decide +kernel
theorem unsat9665 : Unsatisfiable (PosFin 65) f9665 := by
  apply lratCheckerSound f9665 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9665
  · intro a ha; simp [p9665] at ha; subst a; trivial
  · exact checked9665
theorem derived9665 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9665 := by
  apply localUnsat_implies_entails f9665 [c3489, c2892, c3096] c9665 unsat9665 (by rfl) a
  have h0 : Entails.eval a c3489 := h 3488 (by decide)
  have h1 : Entails.eval a c2892 := h 2891 (by decide)
  have h2 : Entails.eval a c3096 := h 3095 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9666 : DefaultClause 65 := directClause [(⟨32, by decide⟩, false), (⟨51, by decide⟩, false), (⟨1, by decide⟩, false), (⟨3, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9666 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c8715, some c9659, some c8812, some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9666 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9666 : lratChecker f9666 p9666 = .success := by decide +kernel
theorem unsat9666 : Unsatisfiable (PosFin 65) f9666 := by
  apply lratCheckerSound f9666 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9666
  · intro a ha; simp [p9666] at ha; subst a; trivial
  · exact checked9666
theorem derived9666 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9666 := by
  apply localUnsat_implies_entails f9666 [c8715, c9659, c8812] c9666 unsat9666 (by rfl) a
  have h0 : Entails.eval a c8715 := derived8715 a h
  have h1 : Entails.eval a c9659 := derived9659 a h
  have h2 : Entails.eval a c8812 := derived8812 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9667 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, false), (⟨32, by decide⟩, true), (⟨29, by decide⟩, true), (⟨51, by decide⟩, false), (⟨12, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9667 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3467, some c3462, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9667 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9667 : lratChecker f9667 p9667 = .success := by decide +kernel
theorem unsat9667 : Unsatisfiable (PosFin 65) f9667 := by
  apply lratCheckerSound f9667 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9667
  · intro a ha; simp [p9667] at ha; subst a; trivial
  · exact checked9667
theorem derived9667 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9667 := by
  apply localUnsat_implies_entails f9667 [c3467, c3462] c9667 unsat9667 (by rfl) a
  have h0 : Entails.eval a c3467 := h 3466 (by decide)
  have h1 : Entails.eval a c3462 := h 3461 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9668 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9668 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9651, some c9658, some c9655, some c9660, some c9662, some c9627, some c9347, some c2113, some c2107, some c9115, some c2103, some c9663, some c2117, some c9666, some c2088, some c9369, some c2075, some c9667, some c852, some c2092, some c635, some c827, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9668 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9668 : lratChecker f9668 p9668 = .success := by decide +kernel
theorem unsat9668 : Unsatisfiable (PosFin 65) f9668 := by
  apply lratCheckerSound f9668 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9668
  · intro a ha; simp [p9668] at ha; subst a; trivial
  · exact checked9668
theorem derived9668 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9668 := by
  apply localUnsat_implies_entails f9668 [c9651, c9658, c9655, c9660, c9662, c9627, c9347, c2113, c2107, c9115, c2103, c9663, c2117, c9666, c2088, c9369, c2075, c9667, c852, c2092, c635, c827] c9668 unsat9668 (by rfl) a
  have h0 : Entails.eval a c9651 := derived9651 a h
  have h1 : Entails.eval a c9658 := derived9658 a h
  have h2 : Entails.eval a c9655 := derived9655 a h
  have h3 : Entails.eval a c9660 := derived9660 a h
  have h4 : Entails.eval a c9662 := derived9662 a h
  have h5 : Entails.eval a c9627 := derived9627 a h
  have h6 : Entails.eval a c9347 := derived9347 a h
  have h7 : Entails.eval a c2113 := h 2112 (by decide)
  have h8 : Entails.eval a c2107 := h 2106 (by decide)
  have h9 : Entails.eval a c9115 := derived9115 a h
  have h10 : Entails.eval a c2103 := h 2102 (by decide)
  have h11 : Entails.eval a c9663 := derived9663 a h
  have h12 : Entails.eval a c2117 := h 2116 (by decide)
  have h13 : Entails.eval a c9666 := derived9666 a h
  have h14 : Entails.eval a c2088 := h 2087 (by decide)
  have h15 : Entails.eval a c9369 := derived9369 a h
  have h16 : Entails.eval a c2075 := h 2074 (by decide)
  have h17 : Entails.eval a c9667 := derived9667 a h
  have h18 : Entails.eval a c852 := h 851 (by decide)
  have h19 : Entails.eval a c2092 := h 2091 (by decide)
  have h20 : Entails.eval a c635 := h 634 (by decide)
  have h21 : Entails.eval a c827 := h 826 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9669 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9669 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9658, some c9651, some c9347, some c9655, some c9660, some c9662, some c9668, some c2861, some c2851, some c9115, some c9666, some c2831, some c2834, some c2823, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9669 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9669 : lratChecker f9669 p9669 = .success := by decide +kernel
theorem unsat9669 : Unsatisfiable (PosFin 65) f9669 := by
  apply lratCheckerSound f9669 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9669
  · intro a ha; simp [p9669] at ha; subst a; trivial
  · exact checked9669
theorem derived9669 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9669 := by
  apply localUnsat_implies_entails f9669 [c9658, c9651, c9347, c9655, c9660, c9662, c9668, c2861, c2851, c9115, c9666, c2831, c2834, c2823] c9669 unsat9669 (by rfl) a
  have h0 : Entails.eval a c9658 := derived9658 a h
  have h1 : Entails.eval a c9651 := derived9651 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9655 := derived9655 a h
  have h4 : Entails.eval a c9660 := derived9660 a h
  have h5 : Entails.eval a c9662 := derived9662 a h
  have h6 : Entails.eval a c9668 := derived9668 a h
  have h7 : Entails.eval a c2861 := h 2860 (by decide)
  have h8 : Entails.eval a c2851 := h 2850 (by decide)
  have h9 : Entails.eval a c9115 := derived9115 a h
  have h10 : Entails.eval a c9666 := derived9666 a h
  have h11 : Entails.eval a c2831 := h 2830 (by decide)
  have h12 : Entails.eval a c2834 := h 2833 (by decide)
  have h13 : Entails.eval a c2823 := h 2822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9670 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9670 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9669, some c9658, some c9627, some c9347, some c9495, some c9497, some c9653, some c1286, some c9477, some c2097, some c2171, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9670 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9670 : lratChecker f9670 p9670 = .success := by decide +kernel
theorem unsat9670 : Unsatisfiable (PosFin 65) f9670 := by
  apply lratCheckerSound f9670 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9670
  · intro a ha; simp [p9670] at ha; subst a; trivial
  · exact checked9670
theorem derived9670 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9670 := by
  apply localUnsat_implies_entails f9670 [c9669, c9658, c9627, c9347, c9495, c9497, c9653, c1286, c9477, c2097, c2171] c9670 unsat9670 (by rfl) a
  have h0 : Entails.eval a c9669 := derived9669 a h
  have h1 : Entails.eval a c9658 := derived9658 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9495 := derived9495 a h
  have h5 : Entails.eval a c9497 := derived9497 a h
  have h6 : Entails.eval a c9653 := derived9653 a h
  have h7 : Entails.eval a c1286 := h 1285 (by decide)
  have h8 : Entails.eval a c9477 := derived9477 a h
  have h9 : Entails.eval a c2097 := h 2096 (by decide)
  have h10 : Entails.eval a c2171 := h 2170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9671 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9671 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9651, some c9658, some c9669, some c9670, some c9660, some c1271, some c1272, some c1303, some c1283, some c1282, some c9508, some c9599, some c1292, some c9565, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9671 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9671 : lratChecker f9671 p9671 = .success := by decide +kernel
theorem unsat9671 : Unsatisfiable (PosFin 65) f9671 := by
  apply lratCheckerSound f9671 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9671
  · intro a ha; simp [p9671] at ha; subst a; trivial
  · exact checked9671
theorem derived9671 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9671 := by
  apply localUnsat_implies_entails f9671 [c9347, c9651, c9658, c9669, c9670, c9660, c1271, c1272, c1303, c1283, c1282, c9508, c9599, c1292, c9565] c9671 unsat9671 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9651 := derived9651 a h
  have h2 : Entails.eval a c9658 := derived9658 a h
  have h3 : Entails.eval a c9669 := derived9669 a h
  have h4 : Entails.eval a c9670 := derived9670 a h
  have h5 : Entails.eval a c9660 := derived9660 a h
  have h6 : Entails.eval a c1271 := h 1270 (by decide)
  have h7 : Entails.eval a c1272 := h 1271 (by decide)
  have h8 : Entails.eval a c1303 := h 1302 (by decide)
  have h9 : Entails.eval a c1283 := h 1282 (by decide)
  have h10 : Entails.eval a c1282 := h 1281 (by decide)
  have h11 : Entails.eval a c9508 := derived9508 a h
  have h12 : Entails.eval a c9599 := derived9599 a h
  have h13 : Entails.eval a c1292 := h 1291 (by decide)
  have h14 : Entails.eval a c9565 := derived9565 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9672 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨12, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9672 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9671, some c9347, some c9129, some c4719, some c2878, some c3149, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9672 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9672 : lratChecker f9672 p9672 = .success := by decide +kernel
theorem unsat9672 : Unsatisfiable (PosFin 65) f9672 := by
  apply lratCheckerSound f9672 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9672
  · intro a ha; simp [p9672] at ha; subst a; trivial
  · exact checked9672
theorem derived9672 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9672 := by
  apply localUnsat_implies_entails f9672 [c9671, c9347, c9129, c4719, c2878, c3149] c9672 unsat9672 (by rfl) a
  have h0 : Entails.eval a c9671 := derived9671 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9129 := derived9129 a h
  have h3 : Entails.eval a c4719 := h 4718 (by decide)
  have h4 : Entails.eval a c2878 := h 2877 (by decide)
  have h5 : Entails.eval a c3149 := h 3148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9673 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9673 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9671, some c9347, some c9672, some c9653, some c9654, some c2842, some c2861, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9673 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9673 : lratChecker f9673 p9673 = .success := by decide +kernel
theorem unsat9673 : Unsatisfiable (PosFin 65) f9673 := by
  apply lratCheckerSound f9673 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9673
  · intro a ha; simp [p9673] at ha; subst a; trivial
  · exact checked9673
theorem derived9673 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9673 := by
  apply localUnsat_implies_entails f9673 [c9671, c9347, c9672, c9653, c9654, c2842, c2861] c9673 unsat9673 (by rfl) a
  have h0 : Entails.eval a c9671 := derived9671 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9672 := derived9672 a h
  have h3 : Entails.eval a c9653 := derived9653 a h
  have h4 : Entails.eval a c9654 := derived9654 a h
  have h5 : Entails.eval a c2842 := h 2841 (by decide)
  have h6 : Entails.eval a c2861 := h 2860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9674 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9674 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2150, some c9035, some c8486, some c8631, some c2137, some c1236, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9674 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9674 : lratChecker f9674 p9674 = .success := by decide +kernel
theorem unsat9674 : Unsatisfiable (PosFin 65) f9674 := by
  apply lratCheckerSound f9674 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9674
  · intro a ha; simp [p9674] at ha; subst a; trivial
  · exact checked9674
theorem derived9674 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9674 := by
  apply localUnsat_implies_entails f9674 [c9627, c2150, c9035, c8486, c8631, c2137, c1236] c9674 unsat9674 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2150 := h 2149 (by decide)
  have h2 : Entails.eval a c9035 := derived9035 a h
  have h3 : Entails.eval a c8486 := derived8486 a h
  have h4 : Entails.eval a c8631 := derived8631 a h
  have h5 : Entails.eval a c2137 := h 2136 (by decide)
  have h6 : Entails.eval a c1236 := h 1235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9675 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨50, by decide⟩, false), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9675 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9671, some c9347, some c9674, some c2674, some c2878, some c3149, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9675 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9675 : lratChecker f9675 p9675 = .success := by decide +kernel
theorem unsat9675 : Unsatisfiable (PosFin 65) f9675 := by
  apply lratCheckerSound f9675 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9675
  · intro a ha; simp [p9675] at ha; subst a; trivial
  · exact checked9675
theorem derived9675 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9675 := by
  apply localUnsat_implies_entails f9675 [c9671, c9347, c9674, c2674, c2878, c3149] c9675 unsat9675 (by rfl) a
  have h0 : Entails.eval a c9671 := derived9671 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9674 := derived9674 a h
  have h3 : Entails.eval a c2674 := h 2673 (by decide)
  have h4 : Entails.eval a c2878 := h 2877 (by decide)
  have h5 : Entails.eval a c3149 := h 3148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9676 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9676 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9673, some c9675, some c9671, some c9627, some c2135, some c1229, some c3404, some c2145, some c4123, some c2139, some c3506, some c4254, some c3978, some c3612, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9676 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9676 : lratChecker f9676 p9676 = .success := by decide +kernel
theorem unsat9676 : Unsatisfiable (PosFin 65) f9676 := by
  apply lratCheckerSound f9676 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9676
  · intro a ha; simp [p9676] at ha; subst a; trivial
  · exact checked9676
theorem derived9676 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9676 := by
  apply localUnsat_implies_entails f9676 [c9673, c9675, c9671, c9627, c2135, c1229, c3404, c2145, c4123, c2139, c3506, c4254, c3978, c3612] c9676 unsat9676 (by rfl) a
  have h0 : Entails.eval a c9673 := derived9673 a h
  have h1 : Entails.eval a c9675 := derived9675 a h
  have h2 : Entails.eval a c9671 := derived9671 a h
  have h3 : Entails.eval a c9627 := derived9627 a h
  have h4 : Entails.eval a c2135 := h 2134 (by decide)
  have h5 : Entails.eval a c1229 := h 1228 (by decide)
  have h6 : Entails.eval a c3404 := h 3403 (by decide)
  have h7 : Entails.eval a c2145 := h 2144 (by decide)
  have h8 : Entails.eval a c4123 := h 4122 (by decide)
  have h9 : Entails.eval a c2139 := h 2138 (by decide)
  have h10 : Entails.eval a c3506 := h 3505 (by decide)
  have h11 : Entails.eval a c4254 := h 4253 (by decide)
  have h12 : Entails.eval a c3978 := h 3977 (by decide)
  have h13 : Entails.eval a c3612 := h 3611 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9677 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨53, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9677 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c2113, some c5029, some c2881, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9677 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9677 : lratChecker f9677 p9677 = .success := by decide +kernel
theorem unsat9677 : Unsatisfiable (PosFin 65) f9677 := by
  apply lratCheckerSound f9677 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9677
  · intro a ha; simp [p9677] at ha; subst a; trivial
  · exact checked9677
theorem derived9677 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9677 := by
  apply localUnsat_implies_entails f9677 [c9627, c9347, c2113, c5029, c2881] c9677 unsat9677 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2113 := h 2112 (by decide)
  have h3 : Entails.eval a c5029 := h 5028 (by decide)
  have h4 : Entails.eval a c2881 := h 2880 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9678 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9678 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9671, some c9347, some c9673, some c9675, some c9676, some c9677, some c2842, some c2861, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9678 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9678 : lratChecker f9678 p9678 = .success := by decide +kernel
theorem unsat9678 : Unsatisfiable (PosFin 65) f9678 := by
  apply lratCheckerSound f9678 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9678
  · intro a ha; simp [p9678] at ha; subst a; trivial
  · exact checked9678
theorem derived9678 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9678 := by
  apply localUnsat_implies_entails f9678 [c9671, c9347, c9673, c9675, c9676, c9677, c2842, c2861] c9678 unsat9678 (by rfl) a
  have h0 : Entails.eval a c9671 := derived9671 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9673 := derived9673 a h
  have h3 : Entails.eval a c9675 := derived9675 a h
  have h4 : Entails.eval a c9676 := derived9676 a h
  have h5 : Entails.eval a c9677 := derived9677 a h
  have h6 : Entails.eval a c2842 := h 2841 (by decide)
  have h7 : Entails.eval a c2861 := h 2860 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9679 : DefaultClause 65 := directClause [(⟨11, by decide⟩, true), (⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9679 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2675, some c2879, some c3150, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p9679 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9679 : lratChecker f9679 p9679 = .success := by decide +kernel
theorem unsat9679 : Unsatisfiable (PosFin 65) f9679 := by
  apply lratCheckerSound f9679 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9679
  · intro a ha; simp [p9679] at ha; subst a; trivial
  · exact checked9679
theorem derived9679 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9679 := by
  apply localUnsat_implies_entails f9679 [c2675, c2879, c3150] c9679 unsat9679 (by rfl) a
  have h0 : Entails.eval a c2675 := h 2674 (by decide)
  have h1 : Entails.eval a c2879 := h 2878 (by decide)
  have h2 : Entails.eval a c3150 := h 3149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9680 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9680 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9671, some c9627, some c9347, some c9678, some c9679, some c4121, some c3403, some c3474, some c2580, some c4182, some c3582, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9680 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9680 : lratChecker f9680 p9680 = .success := by decide +kernel
theorem unsat9680 : Unsatisfiable (PosFin 65) f9680 := by
  apply lratCheckerSound f9680 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9680
  · intro a ha; simp [p9680] at ha; subst a; trivial
  · exact checked9680
theorem derived9680 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9680 := by
  apply localUnsat_implies_entails f9680 [c9671, c9627, c9347, c9678, c9679, c4121, c3403, c3474, c2580, c4182, c3582] c9680 unsat9680 (by rfl) a
  have h0 : Entails.eval a c9671 := derived9671 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9678 := derived9678 a h
  have h4 : Entails.eval a c9679 := derived9679 a h
  have h5 : Entails.eval a c4121 := h 4120 (by decide)
  have h6 : Entails.eval a c3403 := h 3402 (by decide)
  have h7 : Entails.eval a c3474 := h 3473 (by decide)
  have h8 : Entails.eval a c2580 := h 2579 (by decide)
  have h9 : Entails.eval a c4182 := h 4181 (by decide)
  have h10 : Entails.eval a c3582 := h 3581 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9681 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9681 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9680, some c9671, some c9347, some c9495, some c9497, some c9653, some c9477, some c9677, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9681 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9681 : lratChecker f9681 p9681 = .success := by decide +kernel
theorem unsat9681 : Unsatisfiable (PosFin 65) f9681 := by
  apply lratCheckerSound f9681 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9681
  · intro a ha; simp [p9681] at ha; subst a; trivial
  · exact checked9681
theorem derived9681 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9681 := by
  apply localUnsat_implies_entails f9681 [c9680, c9671, c9347, c9495, c9497, c9653, c9477, c9677] c9681 unsat9681 (by rfl) a
  have h0 : Entails.eval a c9680 := derived9680 a h
  have h1 : Entails.eval a c9671 := derived9671 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9495 := derived9495 a h
  have h4 : Entails.eval a c9497 := derived9497 a h
  have h5 : Entails.eval a c9653 := derived9653 a h
  have h6 : Entails.eval a c9477 := derived9477 a h
  have h7 : Entails.eval a c9677 := derived9677 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9682 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9682 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9680, some c9671, some c9347, some c9681, some c1271, some c1272, some c9675, some c1303, some c1286, some c1288, some c3421, some c2548, some c2881, some c3810, some c9484, some c2707, some c3586, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9682 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9682 : lratChecker f9682 p9682 = .success := by decide +kernel
theorem unsat9682 : Unsatisfiable (PosFin 65) f9682 := by
  apply lratCheckerSound f9682 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9682
  · intro a ha; simp [p9682] at ha; subst a; trivial
  · exact checked9682
theorem derived9682 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9682 := by
  apply localUnsat_implies_entails f9682 [c9680, c9671, c9347, c9681, c1271, c1272, c9675, c1303, c1286, c1288, c3421, c2548, c2881, c3810, c9484, c2707, c3586] c9682 unsat9682 (by rfl) a
  have h0 : Entails.eval a c9680 := derived9680 a h
  have h1 : Entails.eval a c9671 := derived9671 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9681 := derived9681 a h
  have h4 : Entails.eval a c1271 := h 1270 (by decide)
  have h5 : Entails.eval a c1272 := h 1271 (by decide)
  have h6 : Entails.eval a c9675 := derived9675 a h
  have h7 : Entails.eval a c1303 := h 1302 (by decide)
  have h8 : Entails.eval a c1286 := h 1285 (by decide)
  have h9 : Entails.eval a c1288 := h 1287 (by decide)
  have h10 : Entails.eval a c3421 := h 3420 (by decide)
  have h11 : Entails.eval a c2548 := h 2547 (by decide)
  have h12 : Entails.eval a c2881 := h 2880 (by decide)
  have h13 : Entails.eval a c3810 := h 3809 (by decide)
  have h14 : Entails.eval a c9484 := derived9484 a h
  have h15 : Entails.eval a c2707 := h 2706 (by decide)
  have h16 : Entails.eval a c3586 := h 3585 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9683 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9683 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9671, some c9680, some c9682, some c3420, some c9612, some c2546, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9683 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9683 : lratChecker f9683 p9683 = .success := by decide +kernel
theorem unsat9683 : Unsatisfiable (PosFin 65) f9683 := by
  apply lratCheckerSound f9683 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9683
  · intro a ha; simp [p9683] at ha; subst a; trivial
  · exact checked9683
theorem derived9683 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9683 := by
  apply localUnsat_implies_entails f9683 [c9347, c9671, c9680, c9682, c3420, c9612, c2546] c9683 unsat9683 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9671 := derived9671 a h
  have h2 : Entails.eval a c9680 := derived9680 a h
  have h3 : Entails.eval a c9682 := derived9682 a h
  have h4 : Entails.eval a c3420 := h 3419 (by decide)
  have h5 : Entails.eval a c9612 := derived9612 a h
  have h6 : Entails.eval a c2546 := h 2545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9684 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9684 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9683, some c8269, some c7994, some c1217, some c1216, some c1238, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9684 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9684 : lratChecker f9684 p9684 = .success := by decide +kernel
theorem unsat9684 : Unsatisfiable (PosFin 65) f9684 := by
  apply lratCheckerSound f9684 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9684
  · intro a ha; simp [p9684] at ha; subst a; trivial
  · exact checked9684
theorem derived9684 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9684 := by
  apply localUnsat_implies_entails f9684 [c9683, c8269, c7994, c1217, c1216, c1238] c9684 unsat9684 (by rfl) a
  have h0 : Entails.eval a c9683 := derived9683 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c7994 := derived7994 a h
  have h3 : Entails.eval a c1217 := h 1216 (by decide)
  have h4 : Entails.eval a c1216 := h 1215 (by decide)
  have h5 : Entails.eval a c1238 := h 1237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9685 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9685 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9683, some c8269, some c9627, some c8420, some c1367, some c2109, some c8409, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9685 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9685 : lratChecker f9685 p9685 = .success := by decide +kernel
theorem unsat9685 : Unsatisfiable (PosFin 65) f9685 := by
  apply lratCheckerSound f9685 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9685
  · intro a ha; simp [p9685] at ha; subst a; trivial
  · exact checked9685
theorem derived9685 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9685 := by
  apply localUnsat_implies_entails f9685 [c9683, c8269, c9627, c8420, c1367, c2109, c8409] c9685 unsat9685 (by rfl) a
  have h0 : Entails.eval a c9683 := derived9683 a h
  have h1 : Entails.eval a c8269 := derived8269 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c8420 := derived8420 a h
  have h4 : Entails.eval a c1367 := h 1366 (by decide)
  have h5 : Entails.eval a c2109 := h 2108 (by decide)
  have h6 : Entails.eval a c8409 := derived8409 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9686 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9686 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9684, some c9683, some c9533, some c7994, some c9347, some c9685, some c9416, some c9415, some c4717, some c3146, some c2876, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9686 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9686 : lratChecker f9686 p9686 = .success := by decide +kernel
theorem unsat9686 : Unsatisfiable (PosFin 65) f9686 := by
  apply lratCheckerSound f9686 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9686
  · intro a ha; simp [p9686] at ha; subst a; trivial
  · exact checked9686
theorem derived9686 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9686 := by
  apply localUnsat_implies_entails f9686 [c9684, c9683, c9533, c7994, c9347, c9685, c9416, c9415, c4717, c3146, c2876] c9686 unsat9686 (by rfl) a
  have h0 : Entails.eval a c9684 := derived9684 a h
  have h1 : Entails.eval a c9683 := derived9683 a h
  have h2 : Entails.eval a c9533 := derived9533 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9685 := derived9685 a h
  have h6 : Entails.eval a c9416 := derived9416 a h
  have h7 : Entails.eval a c9415 := derived9415 a h
  have h8 : Entails.eval a c4717 := h 4716 (by decide)
  have h9 : Entails.eval a c3146 := h 3145 (by decide)
  have h10 : Entails.eval a c2876 := h 2875 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9687 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9687 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9686, some c9684, some c9683, some c9533, some c8269, some c7994, some c9627, some c9347, some c2101, some c9664, some c9665, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9687 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked9687 : lratChecker f9687 p9687 = .success := by decide +kernel
theorem unsat9687 : Unsatisfiable (PosFin 65) f9687 := by
  apply lratCheckerSound f9687 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9687
  · intro a ha; simp [p9687] at ha; subst a; trivial
  · exact checked9687
theorem derived9687 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9687 := by
  apply localUnsat_implies_entails f9687 [c9686, c9684, c9683, c9533, c8269, c7994, c9627, c9347, c2101, c9664, c9665] c9687 unsat9687 (by rfl) a
  have h0 : Entails.eval a c9686 := derived9686 a h
  have h1 : Entails.eval a c9684 := derived9684 a h
  have h2 : Entails.eval a c9683 := derived9683 a h
  have h3 : Entails.eval a c9533 := derived9533 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c9627 := derived9627 a h
  have h7 : Entails.eval a c9347 := derived9347 a h
  have h8 : Entails.eval a c2101 := h 2100 (by decide)
  have h9 : Entails.eval a c9664 := derived9664 a h
  have h10 : Entails.eval a c9665 := derived9665 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9688 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9688 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9684, some c9683, some c9533, some c7994, some c9627, some c9347, some c9686, some c9687, some c9416, some c8300, some c8380, some c2856, some c2534, some c3531, some c3880, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9688 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9688 : lratChecker f9688 p9688 = .success := by decide +kernel
theorem unsat9688 : Unsatisfiable (PosFin 65) f9688 := by
  apply lratCheckerSound f9688 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9688
  · intro a ha; simp [p9688] at ha; subst a; trivial
  · exact checked9688
theorem derived9688 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9688 := by
  apply localUnsat_implies_entails f9688 [c9684, c9683, c9533, c7994, c9627, c9347, c9686, c9687, c9416, c8300, c8380, c2856, c2534, c3531, c3880] c9688 unsat9688 (by rfl) a
  have h0 : Entails.eval a c9684 := derived9684 a h
  have h1 : Entails.eval a c9683 := derived9683 a h
  have h2 : Entails.eval a c9533 := derived9533 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c9627 := derived9627 a h
  have h5 : Entails.eval a c9347 := derived9347 a h
  have h6 : Entails.eval a c9686 := derived9686 a h
  have h7 : Entails.eval a c9687 := derived9687 a h
  have h8 : Entails.eval a c9416 := derived9416 a h
  have h9 : Entails.eval a c8300 := derived8300 a h
  have h10 : Entails.eval a c8380 := derived8380 a h
  have h11 : Entails.eval a c2856 := h 2855 (by decide)
  have h12 : Entails.eval a c2534 := h 2533 (by decide)
  have h13 : Entails.eval a c3531 := h 3530 (by decide)
  have h14 : Entails.eval a c3880 := h 3879 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9689 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨63, by decide⟩, true), (⟨2, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9689 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2839, some c2843, some c9477, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p9689 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9689 : lratChecker f9689 p9689 = .success := by decide +kernel
theorem unsat9689 : Unsatisfiable (PosFin 65) f9689 := by
  apply lratCheckerSound f9689 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9689
  · intro a ha; simp [p9689] at ha; subst a; trivial
  · exact checked9689
theorem derived9689 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9689 := by
  apply localUnsat_implies_entails f9689 [c2839, c2843, c9477] c9689 unsat9689 (by rfl) a
  have h0 : Entails.eval a c2839 := h 2838 (by decide)
  have h1 : Entails.eval a c2843 := h 2842 (by decide)
  have h2 : Entails.eval a c9477 := derived9477 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9690 : DefaultClause 65 := directClause [(⟨3, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9690 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9683, some c7994, some c8269, some c9533, some c9684, some c9688, some c9689, some c2101, some c4451, some c2676, some c4294, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9690 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9690 : lratChecker f9690 p9690 = .success := by decide +kernel
theorem unsat9690 : Unsatisfiable (PosFin 65) f9690 := by
  apply lratCheckerSound f9690 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9690
  · intro a ha; simp [p9690] at ha; subst a; trivial
  · exact checked9690
theorem derived9690 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9690 := by
  apply localUnsat_implies_entails f9690 [c9627, c9347, c9683, c7994, c8269, c9533, c9684, c9688, c9689, c2101, c4451, c2676, c4294] c9690 unsat9690 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9683 := derived9683 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c9533 := derived9533 a h
  have h6 : Entails.eval a c9684 := derived9684 a h
  have h7 : Entails.eval a c9688 := derived9688 a h
  have h8 : Entails.eval a c9689 := derived9689 a h
  have h9 : Entails.eval a c2101 := h 2100 (by decide)
  have h10 : Entails.eval a c4451 := h 4450 (by decide)
  have h11 : Entails.eval a c2676 := h 2675 (by decide)
  have h12 : Entails.eval a c4294 := h 4293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9691 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9691 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9633, some c1419, some c1443, some c1445, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9691 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9691 : lratChecker f9691 p9691 = .success := by decide +kernel
theorem unsat9691 : Unsatisfiable (PosFin 65) f9691 := by
  apply lratCheckerSound f9691 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9691
  · intro a ha; simp [p9691] at ha; subst a; trivial
  · exact checked9691
theorem derived9691 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9691 := by
  apply localUnsat_implies_entails f9691 [c9633, c1419, c1443, c1445] c9691 unsat9691 (by rfl) a
  have h0 : Entails.eval a c9633 := derived9633 a h
  have h1 : Entails.eval a c1419 := h 1418 (by decide)
  have h2 : Entails.eval a c1443 := h 1442 (by decide)
  have h3 : Entails.eval a c1445 := h 1444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9692 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9692 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c2429, some c2430, some c2421, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9692 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9692 : lratChecker f9692 p9692 = .success := by decide +kernel
theorem unsat9692 : Unsatisfiable (PosFin 65) f9692 := by
  apply lratCheckerSound f9692 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9692
  · intro a ha; simp [p9692] at ha; subst a; trivial
  · exact checked9692
theorem derived9692 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9692 := by
  apply localUnsat_implies_entails f9692 [c9690, c9347, c2429, c2430, c2421] c9692 unsat9692 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2429 := h 2428 (by decide)
  have h3 : Entails.eval a c2430 := h 2429 (by decide)
  have h4 : Entails.eval a c2421 := h 2420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9693 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨10, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9693 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2136, some c2138, some c2097, some c2141, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9693 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9693 : lratChecker f9693 p9693 = .success := by decide +kernel
theorem unsat9693 : Unsatisfiable (PosFin 65) f9693 := by
  apply lratCheckerSound f9693 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9693
  · intro a ha; simp [p9693] at ha; subst a; trivial
  · exact checked9693
theorem derived9693 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9693 := by
  apply localUnsat_implies_entails f9693 [c9627, c2136, c2138, c2097, c2141] c9693 unsat9693 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2136 := h 2135 (by decide)
  have h2 : Entails.eval a c2138 := h 2137 (by decide)
  have h3 : Entails.eval a c2097 := h 2096 (by decide)
  have h4 : Entails.eval a c2141 := h 2140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9694 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9694 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9693, some c9627, some c9691, some c2113, some c9692, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9694 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9694 : lratChecker f9694 p9694 = .success := by decide +kernel
theorem unsat9694 : Unsatisfiable (PosFin 65) f9694 := by
  apply lratCheckerSound f9694 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9694
  · intro a ha; simp [p9694] at ha; subst a; trivial
  · exact checked9694
theorem derived9694 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9694 := by
  apply localUnsat_implies_entails f9694 [c9693, c9627, c9691, c2113, c9692] c9694 unsat9694 (by rfl) a
  have h0 : Entails.eval a c9693 := derived9693 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9691 := derived9691 a h
  have h3 : Entails.eval a c2113 := h 2112 (by decide)
  have h4 : Entails.eval a c9692 := derived9692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9695 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9695 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9694, some c2140, some c2151, some c9657, some c3580, some c4118, some c2576, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9695 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9695 : lratChecker f9695 p9695 = .success := by decide +kernel
theorem unsat9695 : Unsatisfiable (PosFin 65) f9695 := by
  apply lratCheckerSound f9695 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9695
  · intro a ha; simp [p9695] at ha; subst a; trivial
  · exact checked9695
theorem derived9695 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9695 := by
  apply localUnsat_implies_entails f9695 [c9627, c9347, c9694, c2140, c2151, c9657, c3580, c4118, c2576] c9695 unsat9695 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9694 := derived9694 a h
  have h3 : Entails.eval a c2140 := h 2139 (by decide)
  have h4 : Entails.eval a c2151 := h 2150 (by decide)
  have h5 : Entails.eval a c9657 := derived9657 a h
  have h6 : Entails.eval a c3580 := h 3579 (by decide)
  have h7 : Entails.eval a c4118 := h 4117 (by decide)
  have h8 : Entails.eval a c2576 := h 2575 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9696 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9696 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c1420, some c2134, some c1445, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9696 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9696 : lratChecker f9696 p9696 = .success := by decide +kernel
theorem unsat9696 : Unsatisfiable (PosFin 65) f9696 := by
  apply lratCheckerSound f9696 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9696
  · intro a ha; simp [p9696] at ha; subst a; trivial
  · exact checked9696
theorem derived9696 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9696 := by
  apply localUnsat_implies_entails f9696 [c9627, c1420, c2134, c1445] c9696 unsat9696 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c1420 := h 1419 (by decide)
  have h2 : Entails.eval a c2134 := h 2133 (by decide)
  have h3 : Entails.eval a c1445 := h 1444 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9697 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨10, by decide⟩, true), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9697 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9696, some c2148, some c9478, some c2138, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9697 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9697 : lratChecker f9697 p9697 = .success := by decide +kernel
theorem unsat9697 : Unsatisfiable (PosFin 65) f9697 := by
  apply lratCheckerSound f9697 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9697
  · intro a ha; simp [p9697] at ha; subst a; trivial
  · exact checked9697
theorem derived9697 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9697 := by
  apply localUnsat_implies_entails f9697 [c9627, c9696, c2148, c9478, c2138] c9697 unsat9697 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9696 := derived9696 a h
  have h2 : Entails.eval a c2148 := h 2147 (by decide)
  have h3 : Entails.eval a c9478 := derived9478 a h
  have h4 : Entails.eval a c2138 := h 2137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9698 : DefaultClause 65 := directClause [(⟨61, by decide⟩, true), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9698 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2136, some c2138, some c2145, some c2141, some (DefaultClause.unit (⟨61, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9698 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9698 : lratChecker f9698 p9698 = .success := by decide +kernel
theorem unsat9698 : Unsatisfiable (PosFin 65) f9698 := by
  apply lratCheckerSound f9698 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9698
  · intro a ha; simp [p9698] at ha; subst a; trivial
  · exact checked9698
theorem derived9698 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9698 := by
  apply localUnsat_implies_entails f9698 [c9627, c2136, c2138, c2145, c2141] c9698 unsat9698 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2136 := h 2135 (by decide)
  have h2 : Entails.eval a c2138 := h 2137 (by decide)
  have h3 : Entails.eval a c2145 := h 2144 (by decide)
  have h4 : Entails.eval a c2141 := h 2140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9699 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9699 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9698, some c9695, some c9690, some c9347, some c9697, some c2485, some c9692, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9699 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9699 : lratChecker f9699 p9699 = .success := by decide +kernel
theorem unsat9699 : Unsatisfiable (PosFin 65) f9699 := by
  apply lratCheckerSound f9699 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9699
  · intro a ha; simp [p9699] at ha; subst a; trivial
  · exact checked9699
theorem derived9699 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9699 := by
  apply localUnsat_implies_entails f9699 [c9698, c9695, c9690, c9347, c9697, c2485, c9692] c9699 unsat9699 (by rfl) a
  have h0 : Entails.eval a c9698 := derived9698 a h
  have h1 : Entails.eval a c9695 := derived9695 a h
  have h2 : Entails.eval a c9690 := derived9690 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9697 := derived9697 a h
  have h5 : Entails.eval a c2485 := h 2484 (by decide)
  have h6 : Entails.eval a c9692 := derived9692 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9700 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9700 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9347, some c9695, some c9699, some c2140, some c2151, some c4118, some c2596, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9700 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked9700 : lratChecker f9700 p9700 = .success := by decide +kernel
theorem unsat9700 : Unsatisfiable (PosFin 65) f9700 := by
  apply lratCheckerSound f9700 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9700
  · intro a ha; simp [p9700] at ha; subst a; trivial
  · exact checked9700
theorem derived9700 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9700 := by
  apply localUnsat_implies_entails f9700 [c9627, c9347, c9695, c9699, c2140, c2151, c4118, c2596] c9700 unsat9700 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9695 := derived9695 a h
  have h3 : Entails.eval a c9699 := derived9699 a h
  have h4 : Entails.eval a c2140 := h 2139 (by decide)
  have h5 : Entails.eval a c2151 := h 2150 (by decide)
  have h6 : Entails.eval a c4118 := h 4117 (by decide)
  have h7 : Entails.eval a c2596 := h 2595 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9701 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9701 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9195, some c8630, some c8436, some c8435, some c2091, some c2089, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9701 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9701 : lratChecker f9701 p9701 = .success := by decide +kernel
theorem unsat9701 : Unsatisfiable (PosFin 65) f9701 := by
  apply lratCheckerSound f9701 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9701
  · intro a ha; simp [p9701] at ha; subst a; trivial
  · exact checked9701
theorem derived9701 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9701 := by
  apply localUnsat_implies_entails f9701 [c9627, c9195, c8630, c8436, c8435, c2091, c2089] c9701 unsat9701 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9195 := derived9195 a h
  have h2 : Entails.eval a c8630 := derived8630 a h
  have h3 : Entails.eval a c8436 := derived8436 a h
  have h4 : Entails.eval a c8435 := derived8435 a h
  have h5 : Entails.eval a c2091 := h 2090 (by decide)
  have h6 : Entails.eval a c2089 := h 2088 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9702 : DefaultClause 65 := directClause [(⟨7, by decide⟩, false), (⟨21, by decide⟩, true), (⟨32, by decide⟩, true), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨50, by decide⟩, false), (⟨49, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9702 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c3550, some c3557, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true))]
def p9702 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9702 : lratChecker f9702 p9702 = .success := by decide +kernel
theorem unsat9702 : Unsatisfiable (PosFin 65) f9702 := by
  apply lratCheckerSound f9702 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9702
  · intro a ha; simp [p9702] at ha; subst a; trivial
  · exact checked9702
theorem derived9702 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9702 := by
  apply localUnsat_implies_entails f9702 [c3550, c3557] c9702 unsat9702 (by rfl) a
  have h0 : Entails.eval a c3550 := h 3549 (by decide)
  have h1 : Entails.eval a c3557 := h 3556 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9703 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9703 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9700, some c9627, some c2135, some c1361, some c8409, some c1445, some c1442, some c2142, some c9445, some c2112, some c9701, some c8496, some c8580, some c1307, some c1313, some c2071, some c8505, some c2132, some c708, some c2094, some c381, some c508, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9703 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked9703 : lratChecker f9703 p9703 = .success := by decide +kernel
theorem unsat9703 : Unsatisfiable (PosFin 65) f9703 := by
  apply lratCheckerSound f9703 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9703
  · intro a ha; simp [p9703] at ha; subst a; trivial
  · exact checked9703
theorem derived9703 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9703 := by
  apply localUnsat_implies_entails f9703 [c9700, c9627, c2135, c1361, c8409, c1445, c1442, c2142, c9445, c2112, c9701, c8496, c8580, c1307, c1313, c2071, c8505, c2132, c708, c2094, c381, c508] c9703 unsat9703 (by rfl) a
  have h0 : Entails.eval a c9700 := derived9700 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c2135 := h 2134 (by decide)
  have h3 : Entails.eval a c1361 := h 1360 (by decide)
  have h4 : Entails.eval a c8409 := derived8409 a h
  have h5 : Entails.eval a c1445 := h 1444 (by decide)
  have h6 : Entails.eval a c1442 := h 1441 (by decide)
  have h7 : Entails.eval a c2142 := h 2141 (by decide)
  have h8 : Entails.eval a c9445 := derived9445 a h
  have h9 : Entails.eval a c2112 := h 2111 (by decide)
  have h10 : Entails.eval a c9701 := derived9701 a h
  have h11 : Entails.eval a c8496 := derived8496 a h
  have h12 : Entails.eval a c8580 := derived8580 a h
  have h13 : Entails.eval a c1307 := h 1306 (by decide)
  have h14 : Entails.eval a c1313 := h 1312 (by decide)
  have h15 : Entails.eval a c2071 := h 2070 (by decide)
  have h16 : Entails.eval a c8505 := derived8505 a h
  have h17 : Entails.eval a c2132 := h 2131 (by decide)
  have h18 : Entails.eval a c708 := h 707 (by decide)
  have h19 : Entails.eval a c2094 := h 2093 (by decide)
  have h20 : Entails.eval a c381 := h 380 (by decide)
  have h21 : Entails.eval a c508 := h 507 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9704 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9704 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2076, some c2075, some c2082, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9704 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9704 : lratChecker f9704 p9704 = .success := by decide +kernel
theorem unsat9704 : Unsatisfiable (PosFin 65) f9704 := by
  apply lratCheckerSound f9704 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9704
  · intro a ha; simp [p9704] at ha; subst a; trivial
  · exact checked9704
theorem derived9704 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9704 := by
  apply localUnsat_implies_entails f9704 [c9627, c2076, c2075, c2082] c9704 unsat9704 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2076 := h 2075 (by decide)
  have h2 : Entails.eval a c2075 := h 2074 (by decide)
  have h3 : Entails.eval a c2082 := h 2081 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9705 : DefaultClause 65 := directClause [(⟨18, by decide⟩, false), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9705 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9627, some c9347, some c2073, some c3461, some c2074, some c2388, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9705 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9705 : lratChecker f9705 p9705 = .success := by decide +kernel
theorem unsat9705 : Unsatisfiable (PosFin 65) f9705 := by
  apply lratCheckerSound f9705 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9705
  · intro a ha; simp [p9705] at ha; subst a; trivial
  · exact checked9705
theorem derived9705 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9705 := by
  apply localUnsat_implies_entails f9705 [c9690, c9627, c9347, c2073, c3461, c2074, c2388] c9705 unsat9705 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2073 := h 2072 (by decide)
  have h4 : Entails.eval a c3461 := h 3460 (by decide)
  have h5 : Entails.eval a c2074 := h 2073 (by decide)
  have h6 : Entails.eval a c2388 := h 2387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9706 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨50, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9706 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9627, some c2135, some c9690, some c2425, some c2444, some c2148, some c2440, some c9705, some c9704, some c3469, some c3468, some c2124, some c2130, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9706 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9706 : lratChecker f9706 p9706 = .success := by decide +kernel
theorem unsat9706 : Unsatisfiable (PosFin 65) f9706 := by
  apply lratCheckerSound f9706 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9706
  · intro a ha; simp [p9706] at ha; subst a; trivial
  · exact checked9706
theorem derived9706 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9706 := by
  apply localUnsat_implies_entails f9706 [c9347, c9627, c2135, c9690, c2425, c2444, c2148, c2440, c9705, c9704, c3469, c3468, c2124, c2130] c9706 unsat9706 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c2135 := h 2134 (by decide)
  have h3 : Entails.eval a c9690 := derived9690 a h
  have h4 : Entails.eval a c2425 := h 2424 (by decide)
  have h5 : Entails.eval a c2444 := h 2443 (by decide)
  have h6 : Entails.eval a c2148 := h 2147 (by decide)
  have h7 : Entails.eval a c2440 := h 2439 (by decide)
  have h8 : Entails.eval a c9705 := derived9705 a h
  have h9 : Entails.eval a c9704 := derived9704 a h
  have h10 : Entails.eval a c3469 := h 3468 (by decide)
  have h11 : Entails.eval a c3468 := h 3467 (by decide)
  have h12 : Entails.eval a c2124 := h 2123 (by decide)
  have h13 : Entails.eval a c2130 := h 2129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9707 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9707 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9704, some c2081, some c2124, some c2125, some c4115, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9707 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9707 : lratChecker f9707 p9707 = .success := by decide +kernel
theorem unsat9707 : Unsatisfiable (PosFin 65) f9707 := by
  apply lratCheckerSound f9707 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9707
  · intro a ha; simp [p9707] at ha; subst a; trivial
  · exact checked9707
theorem derived9707 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9707 := by
  apply localUnsat_implies_entails f9707 [c9627, c9704, c2081, c2124, c2125, c4115] c9707 unsat9707 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9704 := derived9704 a h
  have h2 : Entails.eval a c2081 := h 2080 (by decide)
  have h3 : Entails.eval a c2124 := h 2123 (by decide)
  have h4 : Entails.eval a c2125 := h 2124 (by decide)
  have h5 : Entails.eval a c4115 := h 4114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9708 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9708 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9700, some c9627, some c2135, some c9690, some c9347, some c9703, some c9692, some c2148, some c2425, some c2107, some c2440, some c2444, some c9706, some c9707, some c2074, some c2073, some c4103, some c2388, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9708 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9708 : lratChecker f9708 p9708 = .success := by decide +kernel
theorem unsat9708 : Unsatisfiable (PosFin 65) f9708 := by
  apply lratCheckerSound f9708 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9708
  · intro a ha; simp [p9708] at ha; subst a; trivial
  · exact checked9708
theorem derived9708 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9708 := by
  apply localUnsat_implies_entails f9708 [c9700, c9627, c2135, c9690, c9347, c9703, c9692, c2148, c2425, c2107, c2440, c2444, c9706, c9707, c2074, c2073, c4103, c2388] c9708 unsat9708 (by rfl) a
  have h0 : Entails.eval a c9700 := derived9700 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c2135 := h 2134 (by decide)
  have h3 : Entails.eval a c9690 := derived9690 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c9703 := derived9703 a h
  have h6 : Entails.eval a c9692 := derived9692 a h
  have h7 : Entails.eval a c2148 := h 2147 (by decide)
  have h8 : Entails.eval a c2425 := h 2424 (by decide)
  have h9 : Entails.eval a c2107 := h 2106 (by decide)
  have h10 : Entails.eval a c2440 := h 2439 (by decide)
  have h11 : Entails.eval a c2444 := h 2443 (by decide)
  have h12 : Entails.eval a c9706 := derived9706 a h
  have h13 : Entails.eval a c9707 := derived9707 a h
  have h14 : Entails.eval a c2074 := h 2073 (by decide)
  have h15 : Entails.eval a c2073 := h 2072 (by decide)
  have h16 : Entails.eval a c4103 := h 4102 (by decide)
  have h17 : Entails.eval a c2388 := h 2387 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9709 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9709 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9700, some c9627, some c2135, some c9690, some c9347, some c1421, some c1451, some c2481, some c1423, some c2146, some c9530, some c2150, some c1448, some c2145, some c9195, some c1445, some c8580, some c9516, some c2457, some c3270, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9709 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9709 : lratChecker f9709 p9709 = .success := by decide +kernel
theorem unsat9709 : Unsatisfiable (PosFin 65) f9709 := by
  apply lratCheckerSound f9709 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9709
  · intro a ha; simp [p9709] at ha; subst a; trivial
  · exact checked9709
theorem derived9709 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9709 := by
  apply localUnsat_implies_entails f9709 [c9700, c9627, c2135, c9690, c9347, c1421, c1451, c2481, c1423, c2146, c9530, c2150, c1448, c2145, c9195, c1445, c8580, c9516, c2457, c3270] c9709 unsat9709 (by rfl) a
  have h0 : Entails.eval a c9700 := derived9700 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c2135 := h 2134 (by decide)
  have h3 : Entails.eval a c9690 := derived9690 a h
  have h4 : Entails.eval a c9347 := derived9347 a h
  have h5 : Entails.eval a c1421 := h 1420 (by decide)
  have h6 : Entails.eval a c1451 := h 1450 (by decide)
  have h7 : Entails.eval a c2481 := h 2480 (by decide)
  have h8 : Entails.eval a c1423 := h 1422 (by decide)
  have h9 : Entails.eval a c2146 := h 2145 (by decide)
  have h10 : Entails.eval a c9530 := derived9530 a h
  have h11 : Entails.eval a c2150 := h 2149 (by decide)
  have h12 : Entails.eval a c1448 := h 1447 (by decide)
  have h13 : Entails.eval a c2145 := h 2144 (by decide)
  have h14 : Entails.eval a c9195 := derived9195 a h
  have h15 : Entails.eval a c1445 := h 1444 (by decide)
  have h16 : Entails.eval a c8580 := derived8580 a h
  have h17 : Entails.eval a c9516 := derived9516 a h
  have h18 : Entails.eval a c2457 := h 2456 (by decide)
  have h19 : Entails.eval a c3270 := h 3269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9710 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9710 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2122, some c2123, some c2127, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9710 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9710 : lratChecker f9710 p9710 = .success := by decide +kernel
theorem unsat9710 : Unsatisfiable (PosFin 65) f9710 := by
  apply lratCheckerSound f9710 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9710
  · intro a ha; simp [p9710] at ha; subst a; trivial
  · exact checked9710
theorem derived9710 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9710 := by
  apply localUnsat_implies_entails f9710 [c9627, c2122, c2123, c2127] c9710 unsat9710 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2122 := h 2121 (by decide)
  have h2 : Entails.eval a c2123 := h 2122 (by decide)
  have h3 : Entails.eval a c2127 := h 2126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9711 : DefaultClause 65 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9711 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2124, some c3469, some c3468, some c2130, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9711 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9711 : lratChecker f9711 p9711 = .success := by decide +kernel
theorem unsat9711 : Unsatisfiable (PosFin 65) f9711 := by
  apply lratCheckerSound f9711 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9711
  · intro a ha; simp [p9711] at ha; subst a; trivial
  · exact checked9711
theorem derived9711 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9711 := by
  apply localUnsat_implies_entails f9711 [c9627, c2124, c3469, c3468, c2130] c9711 unsat9711 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2124 := h 2123 (by decide)
  have h2 : Entails.eval a c3469 := h 3468 (by decide)
  have h3 : Entails.eval a c3468 := h 3467 (by decide)
  have h4 : Entails.eval a c2130 := h 2129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9712 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9712 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9710, some c2124, some c9711, some c2125, some c4114, some c2130, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9712 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9712 : lratChecker f9712 p9712 = .success := by decide +kernel
theorem unsat9712 : Unsatisfiable (PosFin 65) f9712 := by
  apply lratCheckerSound f9712 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9712
  · intro a ha; simp [p9712] at ha; subst a; trivial
  · exact checked9712
theorem derived9712 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9712 := by
  apply localUnsat_implies_entails f9712 [c9627, c9710, c2124, c9711, c2125, c4114, c2130] c9712 unsat9712 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9710 := derived9710 a h
  have h2 : Entails.eval a c2124 := h 2123 (by decide)
  have h3 : Entails.eval a c9711 := derived9711 a h
  have h4 : Entails.eval a c2125 := h 2124 (by decide)
  have h5 : Entails.eval a c4114 := h 4113 (by decide)
  have h6 : Entails.eval a c2130 := h 2129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9713 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9713 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9700, some c9690, some c9627, some c9347, some c2135, some c9708, some c9709, some c9692, some c2148, some c2425, some c2145, some c2440, some c2499, some c9712, some c2120, some c2121, some c2388, some c2128, some c3358, some c5035, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9713 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked9713 : lratChecker f9713 p9713 = .success := by decide +kernel
theorem unsat9713 : Unsatisfiable (PosFin 65) f9713 := by
  apply lratCheckerSound f9713 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9713
  · intro a ha; simp [p9713] at ha; subst a; trivial
  · exact checked9713
theorem derived9713 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9713 := by
  apply localUnsat_implies_entails f9713 [c9700, c9690, c9627, c9347, c2135, c9708, c9709, c9692, c2148, c2425, c2145, c2440, c2499, c9712, c2120, c2121, c2388, c2128, c3358, c5035] c9713 unsat9713 (by rfl) a
  have h0 : Entails.eval a c9700 := derived9700 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c2135 := h 2134 (by decide)
  have h5 : Entails.eval a c9708 := derived9708 a h
  have h6 : Entails.eval a c9709 := derived9709 a h
  have h7 : Entails.eval a c9692 := derived9692 a h
  have h8 : Entails.eval a c2148 := h 2147 (by decide)
  have h9 : Entails.eval a c2425 := h 2424 (by decide)
  have h10 : Entails.eval a c2145 := h 2144 (by decide)
  have h11 : Entails.eval a c2440 := h 2439 (by decide)
  have h12 : Entails.eval a c2499 := h 2498 (by decide)
  have h13 : Entails.eval a c9712 := derived9712 a h
  have h14 : Entails.eval a c2120 := h 2119 (by decide)
  have h15 : Entails.eval a c2121 := h 2120 (by decide)
  have h16 : Entails.eval a c2388 := h 2387 (by decide)
  have h17 : Entails.eval a c2128 := h 2127 (by decide)
  have h18 : Entails.eval a c3358 := h 3357 (by decide)
  have h19 : Entails.eval a c5035 := h 5034 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9714 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9714 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9700, some c9713, some c2140, some c2151, some c2144, some c2137, some c5041, some c4117, some c2143, some c2152, some c4260, some c4253, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9714 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9714 : lratChecker f9714 p9714 = .success := by decide +kernel
theorem unsat9714 : Unsatisfiable (PosFin 65) f9714 := by
  apply lratCheckerSound f9714 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9714
  · intro a ha; simp [p9714] at ha; subst a; trivial
  · exact checked9714
theorem derived9714 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9714 := by
  apply localUnsat_implies_entails f9714 [c9627, c9700, c9713, c2140, c2151, c2144, c2137, c5041, c4117, c2143, c2152, c4260, c4253] c9714 unsat9714 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9700 := derived9700 a h
  have h2 : Entails.eval a c9713 := derived9713 a h
  have h3 : Entails.eval a c2140 := h 2139 (by decide)
  have h4 : Entails.eval a c2151 := h 2150 (by decide)
  have h5 : Entails.eval a c2144 := h 2143 (by decide)
  have h6 : Entails.eval a c2137 := h 2136 (by decide)
  have h7 : Entails.eval a c5041 := h 5040 (by decide)
  have h8 : Entails.eval a c4117 := h 4116 (by decide)
  have h9 : Entails.eval a c2143 := h 2142 (by decide)
  have h10 : Entails.eval a c2152 := h 2151 (by decide)
  have h11 : Entails.eval a c4260 := h 4259 (by decide)
  have h12 : Entails.eval a c4253 := h 4252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9715 : DefaultClause 65 := directClause [(⟨50, by decide⟩, true), (⟨56, by decide⟩, true), (⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9715 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2098, some c2099, some c9701, some c8402, some c8496, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9715 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9715 : lratChecker f9715 p9715 = .success := by decide +kernel
theorem unsat9715 : Unsatisfiable (PosFin 65) f9715 := by
  apply lratCheckerSound f9715 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9715
  · intro a ha; simp [p9715] at ha; subst a; trivial
  · exact checked9715
theorem derived9715 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9715 := by
  apply localUnsat_implies_entails f9715 [c9627, c2098, c2099, c9701, c8402, c8496] c9715 unsat9715 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2098 := h 2097 (by decide)
  have h2 : Entails.eval a c2099 := h 2098 (by decide)
  have h3 : Entails.eval a c9701 := derived9701 a h
  have h4 : Entails.eval a c8402 := derived8402 a h
  have h5 : Entails.eval a c8496 := derived8496 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9716 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9716 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9714, some c9627, some c2114, some c8385, some c9715, some c2100, some c1361, some c4388, some c4471, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9716 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9716 : lratChecker f9716 p9716 = .success := by decide +kernel
theorem unsat9716 : Unsatisfiable (PosFin 65) f9716 := by
  apply lratCheckerSound f9716 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9716
  · intro a ha; simp [p9716] at ha; subst a; trivial
  · exact checked9716
theorem derived9716 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9716 := by
  apply localUnsat_implies_entails f9716 [c9714, c9627, c2114, c8385, c9715, c2100, c1361, c4388, c4471] c9716 unsat9716 (by rfl) a
  have h0 : Entails.eval a c9714 := derived9714 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c2114 := h 2113 (by decide)
  have h3 : Entails.eval a c8385 := derived8385 a h
  have h4 : Entails.eval a c9715 := derived9715 a h
  have h5 : Entails.eval a c2100 := h 2099 (by decide)
  have h6 : Entails.eval a c1361 := h 1360 (by decide)
  have h7 : Entails.eval a c4388 := h 4387 (by decide)
  have h8 : Entails.eval a c4471 := h 4470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9717 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9717 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9714, some c9627, some c9347, some c9716, some c9654, some c2113, some c2100, some c2107, some c1372, some c2112, some c9701, some c8496, some c8580, some c8505, some c1317, some c9369, some c9702, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9717 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked9717 : lratChecker f9717 p9717 = .success := by decide +kernel
theorem unsat9717 : Unsatisfiable (PosFin 65) f9717 := by
  apply lratCheckerSound f9717 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9717
  · intro a ha; simp [p9717] at ha; subst a; trivial
  · exact checked9717
theorem derived9717 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9717 := by
  apply localUnsat_implies_entails f9717 [c9714, c9627, c9347, c9716, c9654, c2113, c2100, c2107, c1372, c2112, c9701, c8496, c8580, c8505, c1317, c9369, c9702] c9717 unsat9717 (by rfl) a
  have h0 : Entails.eval a c9714 := derived9714 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9716 := derived9716 a h
  have h4 : Entails.eval a c9654 := derived9654 a h
  have h5 : Entails.eval a c2113 := h 2112 (by decide)
  have h6 : Entails.eval a c2100 := h 2099 (by decide)
  have h7 : Entails.eval a c2107 := h 2106 (by decide)
  have h8 : Entails.eval a c1372 := h 1371 (by decide)
  have h9 : Entails.eval a c2112 := h 2111 (by decide)
  have h10 : Entails.eval a c9701 := derived9701 a h
  have h11 : Entails.eval a c8496 := derived8496 a h
  have h12 : Entails.eval a c8580 := derived8580 a h
  have h13 : Entails.eval a c8505 := derived8505 a h
  have h14 : Entails.eval a c1317 := h 1316 (by decide)
  have h15 : Entails.eval a c9369 := derived9369 a h
  have h16 : Entails.eval a c9702 := derived9702 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9718 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9718 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9704, some c2081, some c2080, some c2077, some c2091, some c2083, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9718 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9718 : lratChecker f9718 p9718 = .success := by decide +kernel
theorem unsat9718 : Unsatisfiable (PosFin 65) f9718 := by
  apply lratCheckerSound f9718 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9718
  · intro a ha; simp [p9718] at ha; subst a; trivial
  · exact checked9718
theorem derived9718 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9718 := by
  apply localUnsat_implies_entails f9718 [c9627, c9704, c2081, c2080, c2077, c2091, c2083] c9718 unsat9718 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9704 := derived9704 a h
  have h2 : Entails.eval a c2081 := h 2080 (by decide)
  have h3 : Entails.eval a c2080 := h 2079 (by decide)
  have h4 : Entails.eval a c2077 := h 2076 (by decide)
  have h5 : Entails.eval a c2091 := h 2090 (by decide)
  have h6 : Entails.eval a c2083 := h 2082 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9719 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9719 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9714, some c9690, some c9627, some c9347, some c9717, some c9692, some c9654, some c2113, some c2425, some c2100, some c2107, some c2440, some c2444, some c2106, some c2112, some c9718, some c2074, some c2073, some c9705, some c2388, some c2086, some c3845, some c3513, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9719 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked9719 : lratChecker f9719 p9719 = .success := by decide +kernel
theorem unsat9719 : Unsatisfiable (PosFin 65) f9719 := by
  apply lratCheckerSound f9719 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9719
  · intro a ha; simp [p9719] at ha; subst a; trivial
  · exact checked9719
theorem derived9719 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9719 := by
  apply localUnsat_implies_entails f9719 [c9714, c9690, c9627, c9347, c9717, c9692, c9654, c2113, c2425, c2100, c2107, c2440, c2444, c2106, c2112, c9718, c2074, c2073, c9705, c2388, c2086, c3845, c3513] c9719 unsat9719 (by rfl) a
  have h0 : Entails.eval a c9714 := derived9714 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9717 := derived9717 a h
  have h5 : Entails.eval a c9692 := derived9692 a h
  have h6 : Entails.eval a c9654 := derived9654 a h
  have h7 : Entails.eval a c2113 := h 2112 (by decide)
  have h8 : Entails.eval a c2425 := h 2424 (by decide)
  have h9 : Entails.eval a c2100 := h 2099 (by decide)
  have h10 : Entails.eval a c2107 := h 2106 (by decide)
  have h11 : Entails.eval a c2440 := h 2439 (by decide)
  have h12 : Entails.eval a c2444 := h 2443 (by decide)
  have h13 : Entails.eval a c2106 := h 2105 (by decide)
  have h14 : Entails.eval a c2112 := h 2111 (by decide)
  have h15 : Entails.eval a c9718 := derived9718 a h
  have h16 : Entails.eval a c2074 := h 2073 (by decide)
  have h17 : Entails.eval a c2073 := h 2072 (by decide)
  have h18 : Entails.eval a c9705 := derived9705 a h
  have h19 : Entails.eval a c2388 := h 2387 (by decide)
  have h20 : Entails.eval a c2086 := h 2085 (by decide)
  have h21 : Entails.eval a c3845 := h 3844 (by decide)
  have h22 : Entails.eval a c3513 := h 3512 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9720 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9720 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c2489, some c9356, some c2838, some c9530, some c2851, some c9195, some c2867, some c2855, some c8496, some c8580, some c9442, some c2870, some c2457, some c8583, some c2452, some c2451, some c2835, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9720 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked9720 : lratChecker f9720 p9720 = .success := by decide +kernel
theorem unsat9720 : Unsatisfiable (PosFin 65) f9720 := by
  apply lratCheckerSound f9720 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9720
  · intro a ha; simp [p9720] at ha; subst a; trivial
  · exact checked9720
theorem derived9720 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9720 := by
  apply localUnsat_implies_entails f9720 [c9690, c9347, c2489, c9356, c2838, c9530, c2851, c9195, c2867, c2855, c8496, c8580, c9442, c2870, c2457, c8583, c2452, c2451, c2835] c9720 unsat9720 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2489 := h 2488 (by decide)
  have h3 : Entails.eval a c9356 := derived9356 a h
  have h4 : Entails.eval a c2838 := h 2837 (by decide)
  have h5 : Entails.eval a c9530 := derived9530 a h
  have h6 : Entails.eval a c2851 := h 2850 (by decide)
  have h7 : Entails.eval a c9195 := derived9195 a h
  have h8 : Entails.eval a c2867 := h 2866 (by decide)
  have h9 : Entails.eval a c2855 := h 2854 (by decide)
  have h10 : Entails.eval a c8496 := derived8496 a h
  have h11 : Entails.eval a c8580 := derived8580 a h
  have h12 : Entails.eval a c9442 := derived9442 a h
  have h13 : Entails.eval a c2870 := h 2869 (by decide)
  have h14 : Entails.eval a c2457 := h 2456 (by decide)
  have h15 : Entails.eval a c8583 := derived8583 a h
  have h16 : Entails.eval a c2452 := h 2451 (by decide)
  have h17 : Entails.eval a c2451 := h 2450 (by decide)
  have h18 : Entails.eval a c2835 := h 2834 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9721 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9721 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c9720, some c2861, some c2860, some c2851, some c2838, some c2480, some c9530, some c9195, some c8496, some c8580, some c2823, some c2457, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9721 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9721 : lratChecker f9721 p9721 = .success := by decide +kernel
theorem unsat9721 : Unsatisfiable (PosFin 65) f9721 := by
  apply lratCheckerSound f9721 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9721
  · intro a ha; simp [p9721] at ha; subst a; trivial
  · exact checked9721
theorem derived9721 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9721 := by
  apply localUnsat_implies_entails f9721 [c9690, c9347, c9720, c2861, c2860, c2851, c2838, c2480, c9530, c9195, c8496, c8580, c2823, c2457] c9721 unsat9721 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9720 := derived9720 a h
  have h3 : Entails.eval a c2861 := h 2860 (by decide)
  have h4 : Entails.eval a c2860 := h 2859 (by decide)
  have h5 : Entails.eval a c2851 := h 2850 (by decide)
  have h6 : Entails.eval a c2838 := h 2837 (by decide)
  have h7 : Entails.eval a c2480 := h 2479 (by decide)
  have h8 : Entails.eval a c9530 := derived9530 a h
  have h9 : Entails.eval a c9195 := derived9195 a h
  have h10 : Entails.eval a c8496 := derived8496 a h
  have h11 : Entails.eval a c8580 := derived8580 a h
  have h12 : Entails.eval a c2823 := h 2822 (by decide)
  have h13 : Entails.eval a c2457 := h 2456 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9722 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9722 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c2460, some c2453, some c2830, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9722 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked9722 : lratChecker f9722 p9722 = .success := by decide +kernel
theorem unsat9722 : Unsatisfiable (PosFin 65) f9722 := by
  apply lratCheckerSound f9722 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9722
  · intro a ha; simp [p9722] at ha; subst a; trivial
  · exact checked9722
theorem derived9722 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9722 := by
  apply localUnsat_implies_entails f9722 [c9690, c9347, c2460, c2453, c2830] c9722 unsat9722 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2460 := h 2459 (by decide)
  have h3 : Entails.eval a c2453 := h 2452 (by decide)
  have h4 : Entails.eval a c2830 := h 2829 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c9723 : DefaultClause 65 := directClause [(⟨20, by decide⟩, true), (⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨55, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9723 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4704, some c4431, some c998, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p9723 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9723 : lratChecker f9723 p9723 = .success := by decide +kernel
theorem unsat9723 : Unsatisfiable (PosFin 65) f9723 := by
  apply lratCheckerSound f9723 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9723
  · intro a ha; simp [p9723] at ha; subst a; trivial
  · exact checked9723
theorem derived9723 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9723 := by
  apply localUnsat_implies_entails f9723 [c4704, c4431, c998] c9723 unsat9723 (by rfl) a
  have h0 : Entails.eval a c4704 := h 4703 (by decide)
  have h1 : Entails.eval a c4431 := h 4430 (by decide)
  have h2 : Entails.eval a c998 := h 997 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9724 : DefaultClause 65 := directClause [(⟨20, by decide⟩, false), (⟨52, by decide⟩, false), (⟨55, by decide⟩, false), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9724 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c2451, some c2453, some c9722, some c2456, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9724 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9724 : lratChecker f9724 p9724 = .success := by decide +kernel
theorem unsat9724 : Unsatisfiable (PosFin 65) f9724 := by
  apply lratCheckerSound f9724 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9724
  · intro a ha; simp [p9724] at ha; subst a; trivial
  · exact checked9724
theorem derived9724 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9724 := by
  apply localUnsat_implies_entails f9724 [c9690, c9347, c2451, c2453, c9722, c2456] c9724 unsat9724 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2451 := h 2450 (by decide)
  have h3 : Entails.eval a c2453 := h 2452 (by decide)
  have h4 : Entails.eval a c9722 := derived9722 a h
  have h5 : Entails.eval a c2456 := h 2455 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9725 : DefaultClause 65 := directClause [(⟨19, by decide⟩, false), (⟨55, by decide⟩, false), (⟨51, by decide⟩, false), (⟨53, by decide⟩, false), (⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨11, by decide⟩, true), (⟨49, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9725 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c2825, some c2826, some c2823, some c2387, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9725 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9725 : lratChecker f9725 p9725 = .success := by decide +kernel
theorem unsat9725 : Unsatisfiable (PosFin 65) f9725 := by
  apply lratCheckerSound f9725 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9725
  · intro a ha; simp [p9725] at ha; subst a; trivial
  · exact checked9725
theorem derived9725 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9725 := by
  apply localUnsat_implies_entails f9725 [c9690, c9347, c2825, c2826, c2823, c2387] c9725 unsat9725 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c2825 := h 2824 (by decide)
  have h3 : Entails.eval a c2826 := h 2825 (by decide)
  have h4 : Entails.eval a c2823 := h 2822 (by decide)
  have h5 : Entails.eval a c2387 := h 2386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9726 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9726 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9714, some c9690, some c9347, some c9719, some c9721, some c9692, some c9477, some c2861, some c2860, some c2851, some c2440, some c2838, some c2431, some c2490, some c2480, some c2445, some c2469, some c8007, some c9724, some c9725, some c9723, some c2832, some c2833, some c3272, some c3463, some c977, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9726 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked9726 : lratChecker f9726 p9726 = .success := by decide +kernel
theorem unsat9726 : Unsatisfiable (PosFin 65) f9726 := by
  apply lratCheckerSound f9726 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9726
  · intro a ha; simp [p9726] at ha; subst a; trivial
  · exact checked9726
theorem derived9726 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9726 := by
  apply localUnsat_implies_entails f9726 [c9714, c9690, c9347, c9719, c9721, c9692, c9477, c2861, c2860, c2851, c2440, c2838, c2431, c2490, c2480, c2445, c2469, c8007, c9724, c9725, c9723, c2832, c2833, c3272, c3463, c977] c9726 unsat9726 (by rfl) a
  have h0 : Entails.eval a c9714 := derived9714 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9719 := derived9719 a h
  have h4 : Entails.eval a c9721 := derived9721 a h
  have h5 : Entails.eval a c9692 := derived9692 a h
  have h6 : Entails.eval a c9477 := derived9477 a h
  have h7 : Entails.eval a c2861 := h 2860 (by decide)
  have h8 : Entails.eval a c2860 := h 2859 (by decide)
  have h9 : Entails.eval a c2851 := h 2850 (by decide)
  have h10 : Entails.eval a c2440 := h 2439 (by decide)
  have h11 : Entails.eval a c2838 := h 2837 (by decide)
  have h12 : Entails.eval a c2431 := h 2430 (by decide)
  have h13 : Entails.eval a c2490 := h 2489 (by decide)
  have h14 : Entails.eval a c2480 := h 2479 (by decide)
  have h15 : Entails.eval a c2445 := h 2444 (by decide)
  have h16 : Entails.eval a c2469 := h 2468 (by decide)
  have h17 : Entails.eval a c8007 := derived8007 a h
  have h18 : Entails.eval a c9724 := derived9724 a h
  have h19 : Entails.eval a c9725 := derived9725 a h
  have h20 : Entails.eval a c9723 := derived9723 a h
  have h21 : Entails.eval a c2832 := h 2831 (by decide)
  have h22 : Entails.eval a c2833 := h 2832 (by decide)
  have h23 : Entails.eval a c3272 := h 3271 (by decide)
  have h24 : Entails.eval a c3463 := h 3462 (by decide)
  have h25 : Entails.eval a c977 := h 976 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9727 : DefaultClause 65 := directClause [(⟨12, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9727 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c9714, some c9726, some c9648, some c9657, some c2437, some c2846, some c2838, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9727 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9727 : lratChecker f9727 p9727 = .success := by decide +kernel
theorem unsat9727 : Unsatisfiable (PosFin 65) f9727 := by
  apply lratCheckerSound f9727 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9727
  · intro a ha; simp [p9727] at ha; subst a; trivial
  · exact checked9727
theorem derived9727 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9727 := by
  apply localUnsat_implies_entails f9727 [c9690, c9347, c9714, c9726, c9648, c9657, c2437, c2846, c2838] c9727 unsat9727 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9714 := derived9714 a h
  have h3 : Entails.eval a c9726 := derived9726 a h
  have h4 : Entails.eval a c9648 := derived9648 a h
  have h5 : Entails.eval a c9657 := derived9657 a h
  have h6 : Entails.eval a c2437 := h 2436 (by decide)
  have h7 : Entails.eval a c2846 := h 2845 (by decide)
  have h8 : Entails.eval a c2838 := h 2837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9728 : DefaultClause 65 := directClause [(⟨53, by decide⟩, true), (⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9728 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c2114, some c8385, some c9715, some c2100, some c1361, some c1394, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9728 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked9728 : lratChecker f9728 p9728 = .success := by decide +kernel
theorem unsat9728 : Unsatisfiable (PosFin 65) f9728 := by
  apply lratCheckerSound f9728 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9728
  · intro a ha; simp [p9728] at ha; subst a; trivial
  · exact checked9728
theorem derived9728 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9728 := by
  apply localUnsat_implies_entails f9728 [c9627, c2114, c8385, c9715, c2100, c1361, c1394] c9728 unsat9728 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c2114 := h 2113 (by decide)
  have h2 : Entails.eval a c8385 := derived8385 a h
  have h3 : Entails.eval a c9715 := derived9715 a h
  have h4 : Entails.eval a c2100 := h 2099 (by decide)
  have h5 : Entails.eval a c1361 := h 1360 (by decide)
  have h6 : Entails.eval a c1394 := h 1393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9729 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9729 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9727, some c9627, some c9347, some c9703, some c9728, some c2113, some c9633, some c1379, some c9599, some c2100, some c2176, some c9701, some c9528, some c8496, some c8580, some c1317, some c9562, some c9702, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9729 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked9729 : lratChecker f9729 p9729 = .success := by decide +kernel
theorem unsat9729 : Unsatisfiable (PosFin 65) f9729 := by
  apply lratCheckerSound f9729 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9729
  · intro a ha; simp [p9729] at ha; subst a; trivial
  · exact checked9729
theorem derived9729 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9729 := by
  apply localUnsat_implies_entails f9729 [c9727, c9627, c9347, c9703, c9728, c2113, c9633, c1379, c9599, c2100, c2176, c9701, c9528, c8496, c8580, c1317, c9562, c9702] c9729 unsat9729 (by rfl) a
  have h0 : Entails.eval a c9727 := derived9727 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9703 := derived9703 a h
  have h4 : Entails.eval a c9728 := derived9728 a h
  have h5 : Entails.eval a c2113 := h 2112 (by decide)
  have h6 : Entails.eval a c9633 := derived9633 a h
  have h7 : Entails.eval a c1379 := h 1378 (by decide)
  have h8 : Entails.eval a c9599 := derived9599 a h
  have h9 : Entails.eval a c2100 := h 2099 (by decide)
  have h10 : Entails.eval a c2176 := h 2175 (by decide)
  have h11 : Entails.eval a c9701 := derived9701 a h
  have h12 : Entails.eval a c9528 := derived9528 a h
  have h13 : Entails.eval a c8496 := derived8496 a h
  have h14 : Entails.eval a c8580 := derived8580 a h
  have h15 : Entails.eval a c1317 := h 1316 (by decide)
  have h16 : Entails.eval a c9562 := derived9562 a h
  have h17 : Entails.eval a c9702 := derived9702 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9730 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9730 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9727, some c9690, some c9627, some c9347, some c9729, some c9692, some c2113, some c2425, some c2107, some c2440, some c2103, some c2106, some c2431, some c2432, some c8007, some c2112, some c2445, some c9718, some c2153, some c2154, some c2156, some c2388, some c5090, some c2538, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9730 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked9730 : lratChecker f9730 p9730 = .success := by decide +kernel
theorem unsat9730 : Unsatisfiable (PosFin 65) f9730 := by
  apply lratCheckerSound f9730 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9730
  · intro a ha; simp [p9730] at ha; subst a; trivial
  · exact checked9730
theorem derived9730 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9730 := by
  apply localUnsat_implies_entails f9730 [c9727, c9690, c9627, c9347, c9729, c9692, c2113, c2425, c2107, c2440, c2103, c2106, c2431, c2432, c8007, c2112, c2445, c9718, c2153, c2154, c2156, c2388, c5090, c2538] c9730 unsat9730 (by rfl) a
  have h0 : Entails.eval a c9727 := derived9727 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9729 := derived9729 a h
  have h5 : Entails.eval a c9692 := derived9692 a h
  have h6 : Entails.eval a c2113 := h 2112 (by decide)
  have h7 : Entails.eval a c2425 := h 2424 (by decide)
  have h8 : Entails.eval a c2107 := h 2106 (by decide)
  have h9 : Entails.eval a c2440 := h 2439 (by decide)
  have h10 : Entails.eval a c2103 := h 2102 (by decide)
  have h11 : Entails.eval a c2106 := h 2105 (by decide)
  have h12 : Entails.eval a c2431 := h 2430 (by decide)
  have h13 : Entails.eval a c2432 := h 2431 (by decide)
  have h14 : Entails.eval a c8007 := derived8007 a h
  have h15 : Entails.eval a c2112 := h 2111 (by decide)
  have h16 : Entails.eval a c2445 := h 2444 (by decide)
  have h17 : Entails.eval a c9718 := derived9718 a h
  have h18 : Entails.eval a c2153 := h 2152 (by decide)
  have h19 : Entails.eval a c2154 := h 2153 (by decide)
  have h20 : Entails.eval a c2156 := h 2155 (by decide)
  have h21 : Entails.eval a c2388 := h 2387 (by decide)
  have h22 : Entails.eval a c5090 := h 5089 (by decide)
  have h23 : Entails.eval a c2538 := h 2537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9731 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, false), (⟨10, by decide⟩, true), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9731 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9709, some c9721, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9731 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9731 : lratChecker f9731 p9731 = .success := by decide +kernel
theorem unsat9731 : Unsatisfiable (PosFin 65) f9731 := by
  apply lratCheckerSound f9731 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9731
  · intro a ha; simp [p9731] at ha; subst a; trivial
  · exact checked9731
theorem derived9731 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9731 := by
  apply localUnsat_implies_entails f9731 [c9709, c9721] c9731 unsat9731 (by rfl) a
  have h0 : Entails.eval a c9709 := derived9709 a h
  have h1 : Entails.eval a c9721 := derived9721 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9732 : DefaultClause 65 := directClause [(⟨19, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9732 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2124, some c2125, some c2126, some c2130, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p9732 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9732 : lratChecker f9732 p9732 = .success := by decide +kernel
theorem unsat9732 : Unsatisfiable (PosFin 65) f9732 := by
  apply lratCheckerSound f9732 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9732
  · intro a ha; simp [p9732] at ha; subst a; trivial
  · exact checked9732
theorem derived9732 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9732 := by
  apply localUnsat_implies_entails f9732 [c2124, c2125, c2126, c2130] c9732 unsat9732 (by rfl) a
  have h0 : Entails.eval a c2124 := h 2123 (by decide)
  have h1 : Entails.eval a c2125 := h 2124 (by decide)
  have h2 : Entails.eval a c2126 := h 2125 (by decide)
  have h3 : Entails.eval a c2130 := h 2129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9733 : DefaultClause 65 := directClause [(⟨18, by decide⟩, true), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨55, by decide⟩, false), (⟨53, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9733 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9627, some c9710, some c9732, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9733 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked9733 : lratChecker f9733 p9733 = .success := by decide +kernel
theorem unsat9733 : Unsatisfiable (PosFin 65) f9733 := by
  apply lratCheckerSound f9733 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9733
  · intro a ha; simp [p9733] at ha; subst a; trivial
  · exact checked9733
theorem derived9733 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9733 := by
  apply localUnsat_implies_entails f9733 [c9627, c9710, c9732] c9733 unsat9733 (by rfl) a
  have h0 : Entails.eval a c9627 := derived9627 a h
  have h1 : Entails.eval a c9710 := derived9710 a h
  have h2 : Entails.eval a c9732 := derived9732 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c9734 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9734 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9730, some c9731, some c9690, some c9347, some c9692, some c2425, some c2426, some c2440, some c2490, some c2431, some c2445, some c2427, some c2481, some c2469, some c8007, some c9727, some c9627, some c2145, some c9733, some c2120, some c2121, some c2455, some c2128, some c3270, some c4965, some c2538, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9734 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked9734 : lratChecker f9734 p9734 = .success := by decide +kernel
theorem unsat9734 : Unsatisfiable (PosFin 65) f9734 := by
  apply lratCheckerSound f9734 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9734
  · intro a ha; simp [p9734] at ha; subst a; trivial
  · exact checked9734
theorem derived9734 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9734 := by
  apply localUnsat_implies_entails f9734 [c9730, c9731, c9690, c9347, c9692, c2425, c2426, c2440, c2490, c2431, c2445, c2427, c2481, c2469, c8007, c9727, c9627, c2145, c9733, c2120, c2121, c2455, c2128, c3270, c4965, c2538] c9734 unsat9734 (by rfl) a
  have h0 : Entails.eval a c9730 := derived9730 a h
  have h1 : Entails.eval a c9731 := derived9731 a h
  have h2 : Entails.eval a c9690 := derived9690 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9692 := derived9692 a h
  have h5 : Entails.eval a c2425 := h 2424 (by decide)
  have h6 : Entails.eval a c2426 := h 2425 (by decide)
  have h7 : Entails.eval a c2440 := h 2439 (by decide)
  have h8 : Entails.eval a c2490 := h 2489 (by decide)
  have h9 : Entails.eval a c2431 := h 2430 (by decide)
  have h10 : Entails.eval a c2445 := h 2444 (by decide)
  have h11 : Entails.eval a c2427 := h 2426 (by decide)
  have h12 : Entails.eval a c2481 := h 2480 (by decide)
  have h13 : Entails.eval a c2469 := h 2468 (by decide)
  have h14 : Entails.eval a c8007 := derived8007 a h
  have h15 : Entails.eval a c9727 := derived9727 a h
  have h16 : Entails.eval a c9627 := derived9627 a h
  have h17 : Entails.eval a c2145 := h 2144 (by decide)
  have h18 : Entails.eval a c9733 := derived9733 a h
  have h19 : Entails.eval a c2120 := h 2119 (by decide)
  have h20 : Entails.eval a c2121 := h 2120 (by decide)
  have h21 : Entails.eval a c2455 := h 2454 (by decide)
  have h22 : Entails.eval a c2128 := h 2127 (by decide)
  have h23 : Entails.eval a c3270 := h 3269 (by decide)
  have h24 : Entails.eval a c4965 := h 4964 (by decide)
  have h25 : Entails.eval a c2538 := h 2537 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9735 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9735 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9727, some c9690, some c9347, some c9730, some c9731, some c9692, some c2425, some c2426, some c2440, some c2490, some c2481, some c9734, some c9599, some c9725, some c9724, some c2833, some c2832, some c2393, some c2449, some c2385, some c2397, some c2828, some c2395, some c2379, some c2390, some c2412, some c2836, some c2400, some c2383, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9735 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked9735 : lratChecker f9735 p9735 = .success := by decide +kernel
theorem unsat9735 : Unsatisfiable (PosFin 65) f9735 := by
  apply lratCheckerSound f9735 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9735
  · intro a ha; simp [p9735] at ha; subst a; trivial
  · exact checked9735
theorem derived9735 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9735 := by
  apply localUnsat_implies_entails f9735 [c9727, c9690, c9347, c9730, c9731, c9692, c2425, c2426, c2440, c2490, c2481, c9734, c9599, c9725, c9724, c2833, c2832, c2393, c2449, c2385, c2397, c2828, c2395, c2379, c2390, c2412, c2836, c2400, c2383] c9735 unsat9735 (by rfl) a
  have h0 : Entails.eval a c9727 := derived9727 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9730 := derived9730 a h
  have h4 : Entails.eval a c9731 := derived9731 a h
  have h5 : Entails.eval a c9692 := derived9692 a h
  have h6 : Entails.eval a c2425 := h 2424 (by decide)
  have h7 : Entails.eval a c2426 := h 2425 (by decide)
  have h8 : Entails.eval a c2440 := h 2439 (by decide)
  have h9 : Entails.eval a c2490 := h 2489 (by decide)
  have h10 : Entails.eval a c2481 := h 2480 (by decide)
  have h11 : Entails.eval a c9734 := derived9734 a h
  have h12 : Entails.eval a c9599 := derived9599 a h
  have h13 : Entails.eval a c9725 := derived9725 a h
  have h14 : Entails.eval a c9724 := derived9724 a h
  have h15 : Entails.eval a c2833 := h 2832 (by decide)
  have h16 : Entails.eval a c2832 := h 2831 (by decide)
  have h17 : Entails.eval a c2393 := h 2392 (by decide)
  have h18 : Entails.eval a c2449 := h 2448 (by decide)
  have h19 : Entails.eval a c2385 := h 2384 (by decide)
  have h20 : Entails.eval a c2397 := h 2396 (by decide)
  have h21 : Entails.eval a c2828 := h 2827 (by decide)
  have h22 : Entails.eval a c2395 := h 2394 (by decide)
  have h23 : Entails.eval a c2379 := h 2378 (by decide)
  have h24 : Entails.eval a c2390 := h 2389 (by decide)
  have h25 : Entails.eval a c2412 := h 2411 (by decide)
  have h26 : Entails.eval a c2836 := h 2835 (by decide)
  have h27 : Entails.eval a c2400 := h 2399 (by decide)
  have h28 : Entails.eval a c2383 := h 2382 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9736 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9736 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9735, some c9690, some c9627, some c9347, some c9648, some c1447, some c9700, some c3806, some c2140, some c2143, some c5042, some c2144, some c2519, some c2514, some c3448, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9736 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked9736 : lratChecker f9736 p9736 = .success := by decide +kernel
theorem unsat9736 : Unsatisfiable (PosFin 65) f9736 := by
  apply lratCheckerSound f9736 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9736
  · intro a ha; simp [p9736] at ha; subst a; trivial
  · exact checked9736
theorem derived9736 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9736 := by
  apply localUnsat_implies_entails f9736 [c9735, c9690, c9627, c9347, c9648, c1447, c9700, c3806, c2140, c2143, c5042, c2144, c2519, c2514, c3448] c9736 unsat9736 (by rfl) a
  have h0 : Entails.eval a c9735 := derived9735 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9648 := derived9648 a h
  have h5 : Entails.eval a c1447 := h 1446 (by decide)
  have h6 : Entails.eval a c9700 := derived9700 a h
  have h7 : Entails.eval a c3806 := h 3805 (by decide)
  have h8 : Entails.eval a c2140 := h 2139 (by decide)
  have h9 : Entails.eval a c2143 := h 2142 (by decide)
  have h10 : Entails.eval a c5042 := h 5041 (by decide)
  have h11 : Entails.eval a c2144 := h 2143 (by decide)
  have h12 : Entails.eval a c2519 := h 2518 (by decide)
  have h13 : Entails.eval a c2514 := h 2513 (by decide)
  have h14 : Entails.eval a c3448 := h 3447 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9737 : DefaultClause 65 := directClause [(⟨11, by decide⟩, false), (⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9737 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9735, some c9690, some c9736, some c2437, some c9657, some c9627, some c9700, some c5041, some c3373, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9737 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9737 : lratChecker f9737 p9737 = .success := by decide +kernel
theorem unsat9737 : Unsatisfiable (PosFin 65) f9737 := by
  apply lratCheckerSound f9737 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9737
  · intro a ha; simp [p9737] at ha; subst a; trivial
  · exact checked9737
theorem derived9737 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9737 := by
  apply localUnsat_implies_entails f9737 [c9347, c9735, c9690, c9736, c2437, c9657, c9627, c9700, c5041, c3373] c9737 unsat9737 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9735 := derived9735 a h
  have h2 : Entails.eval a c9690 := derived9690 a h
  have h3 : Entails.eval a c9736 := derived9736 a h
  have h4 : Entails.eval a c2437 := h 2436 (by decide)
  have h5 : Entails.eval a c9657 := derived9657 a h
  have h6 : Entails.eval a c9627 := derived9627 a h
  have h7 : Entails.eval a c9700 := derived9700 a h
  have h8 : Entails.eval a c5041 := h 5040 (by decide)
  have h9 : Entails.eval a c3373 := h 3372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9738 : DefaultClause 65 := directClause [(⟨49, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9738 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c9735, some c9736, some c9657, some c2437, some c9737, some c2846, some c2838, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9738 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9738 : lratChecker f9738 p9738 = .success := by decide +kernel
theorem unsat9738 : Unsatisfiable (PosFin 65) f9738 := by
  apply lratCheckerSound f9738 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9738
  · intro a ha; simp [p9738] at ha; subst a; trivial
  · exact checked9738
theorem derived9738 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9738 := by
  apply localUnsat_implies_entails f9738 [c9690, c9347, c9735, c9736, c9657, c2437, c9737, c2846, c2838] c9738 unsat9738 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9735 := derived9735 a h
  have h3 : Entails.eval a c9736 := derived9736 a h
  have h4 : Entails.eval a c9657 := derived9657 a h
  have h5 : Entails.eval a c2437 := h 2436 (by decide)
  have h6 : Entails.eval a c9737 := derived9737 a h
  have h7 : Entails.eval a c2846 := h 2845 (by decide)
  have h8 : Entails.eval a c2838 := h 2837 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9739 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9739 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9738, some c9627, some c9347, some c9691, some c2135, some c1361, some c1394, some c8385, some c2114, some c2113, some c9476, some c9445, some c4123, some c2584, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9739 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked9739 : lratChecker f9739 p9739 = .success := by decide +kernel
theorem unsat9739 : Unsatisfiable (PosFin 65) f9739 := by
  apply lratCheckerSound f9739 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9739
  · intro a ha; simp [p9739] at ha; subst a; trivial
  · exact checked9739
theorem derived9739 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9739 := by
  apply localUnsat_implies_entails f9739 [c9738, c9627, c9347, c9691, c2135, c1361, c1394, c8385, c2114, c2113, c9476, c9445, c4123, c2584] c9739 unsat9739 (by rfl) a
  have h0 : Entails.eval a c9738 := derived9738 a h
  have h1 : Entails.eval a c9627 := derived9627 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9691 := derived9691 a h
  have h4 : Entails.eval a c2135 := h 2134 (by decide)
  have h5 : Entails.eval a c1361 := h 1360 (by decide)
  have h6 : Entails.eval a c1394 := h 1393 (by decide)
  have h7 : Entails.eval a c8385 := derived8385 a h
  have h8 : Entails.eval a c2114 := h 2113 (by decide)
  have h9 : Entails.eval a c2113 := h 2112 (by decide)
  have h10 : Entails.eval a c9476 := derived9476 a h
  have h11 : Entails.eval a c9445 := derived9445 a h
  have h12 : Entails.eval a c4123 := h 4122 (by decide)
  have h13 : Entails.eval a c2584 := h 2583 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9740 : DefaultClause 65 := directClause [(⟨10, by decide⟩, true), (⟨54, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9740 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9738, some c9690, some c9347, some c2475, some c2471, some c2485, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9740 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked9740 : lratChecker f9740 p9740 = .success := by decide +kernel
theorem unsat9740 : Unsatisfiable (PosFin 65) f9740 := by
  apply lratCheckerSound f9740 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9740
  · intro a ha; simp [p9740] at ha; subst a; trivial
  · exact checked9740
theorem derived9740 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9740 := by
  apply localUnsat_implies_entails f9740 [c9738, c9690, c9347, c2475, c2471, c2485] c9740 unsat9740 (by rfl) a
  have h0 : Entails.eval a c9738 := derived9738 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c2475 := h 2474 (by decide)
  have h4 : Entails.eval a c2471 := h 2470 (by decide)
  have h5 : Entails.eval a c2485 := h 2484 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9741 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨11, by decide⟩, false), (⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9741 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9738, some c9690, some c9627, some c9347, some c9740, some c9739, some c2423, some c2417, some c2113, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9741 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9741 : lratChecker f9741 p9741 = .success := by decide +kernel
theorem unsat9741 : Unsatisfiable (PosFin 65) f9741 := by
  apply lratCheckerSound f9741 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9741
  · intro a ha; simp [p9741] at ha; subst a; trivial
  · exact checked9741
theorem derived9741 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9741 := by
  apply localUnsat_implies_entails f9741 [c9738, c9690, c9627, c9347, c9740, c9739, c2423, c2417, c2113] c9741 unsat9741 (by rfl) a
  have h0 : Entails.eval a c9738 := derived9738 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9627 := derived9627 a h
  have h3 : Entails.eval a c9347 := derived9347 a h
  have h4 : Entails.eval a c9740 := derived9740 a h
  have h5 : Entails.eval a c9739 := derived9739 a h
  have h6 : Entails.eval a c2423 := h 2422 (by decide)
  have h7 : Entails.eval a c2417 := h 2416 (by decide)
  have h8 : Entails.eval a c2113 := h 2112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9742 : DefaultClause 65 := directClause [(⟨54, by decide⟩, true), (⟨49, by decide⟩, true), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨64, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f9742 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c2508, some c2472, some c2419, some c3789, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨64, by decide⟩, false))]
def p9742 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9742 : lratChecker f9742 p9742 = .success := by decide +kernel
theorem unsat9742 : Unsatisfiable (PosFin 65) f9742 := by
  apply lratCheckerSound f9742 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9742
  · intro a ha; simp [p9742] at ha; subst a; trivial
  · exact checked9742
theorem derived9742 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9742 := by
  apply localUnsat_implies_entails f9742 [c2508, c2472, c2419, c3789] c9742 unsat9742 (by rfl) a
  have h0 : Entails.eval a c2508 := h 2507 (by decide)
  have h1 : Entails.eval a c2472 := h 2471 (by decide)
  have h2 : Entails.eval a c2419 := h 2418 (by decide)
  have h3 : Entails.eval a c3789 := h 3788 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c9743 : DefaultClause 65 := directClause [(⟨64, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9743 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c9738, some c9742, some c9740, some c9741, some c9677, some c2417, some c2674, some c3581, some (DefaultClause.unit (⟨64, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9743 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked9743 : lratChecker f9743 p9743 = .success := by decide +kernel
theorem unsat9743 : Unsatisfiable (PosFin 65) f9743 := by
  apply lratCheckerSound f9743 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9743
  · intro a ha; simp [p9743] at ha; subst a; trivial
  · exact checked9743
theorem derived9743 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9743 := by
  apply localUnsat_implies_entails f9743 [c9690, c9347, c9738, c9742, c9740, c9741, c9677, c2417, c2674, c3581] c9743 unsat9743 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9738 := derived9738 a h
  have h3 : Entails.eval a c9742 := derived9742 a h
  have h4 : Entails.eval a c9740 := derived9740 a h
  have h5 : Entails.eval a c9741 := derived9741 a h
  have h6 : Entails.eval a c9677 := derived9677 a h
  have h7 : Entails.eval a c2417 := h 2416 (by decide)
  have h8 : Entails.eval a c2674 := h 2673 (by decide)
  have h9 : Entails.eval a c3581 := h 3580 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9744 : DefaultClause 65 := directClause [(⟨4, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9744 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c9743, some c8383, some c8269, some c7994, some c9627, some c9467, some c9416, some c2101, some c1361, some c1394, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9744 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9744 : lratChecker f9744 p9744 = .success := by decide +kernel
theorem unsat9744 : Unsatisfiable (PosFin 65) f9744 := by
  apply lratCheckerSound f9744 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9744
  · intro a ha; simp [p9744] at ha; subst a; trivial
  · exact checked9744
theorem derived9744 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9744 := by
  apply localUnsat_implies_entails f9744 [c9690, c9347, c9743, c8383, c8269, c7994, c9627, c9467, c9416, c2101, c1361, c1394] c9744 unsat9744 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9743 := derived9743 a h
  have h3 : Entails.eval a c8383 := derived8383 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c7994 := derived7994 a h
  have h6 : Entails.eval a c9627 := derived9627 a h
  have h7 : Entails.eval a c9467 := derived9467 a h
  have h8 : Entails.eval a c9416 := derived9416 a h
  have h9 : Entails.eval a c2101 := h 2100 (by decide)
  have h10 : Entails.eval a c1361 := h 1360 (by decide)
  have h11 : Entails.eval a c1394 := h 1393 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9745 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨54, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9745 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9744, some c9690, some c9347, some c9743, some c8383, some c8269, some c7994, some c9627, some c2101, some c2108, some c2444, some c2425, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9745 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked9745 : lratChecker f9745 p9745 = .success := by decide +kernel
theorem unsat9745 : Unsatisfiable (PosFin 65) f9745 := by
  apply lratCheckerSound f9745 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9745
  · intro a ha; simp [p9745] at ha; subst a; trivial
  · exact checked9745
theorem derived9745 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9745 := by
  apply localUnsat_implies_entails f9745 [c9744, c9690, c9347, c9743, c8383, c8269, c7994, c9627, c2101, c2108, c2444, c2425] c9745 unsat9745 (by rfl) a
  have h0 : Entails.eval a c9744 := derived9744 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9743 := derived9743 a h
  have h4 : Entails.eval a c8383 := derived8383 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c7994 := derived7994 a h
  have h7 : Entails.eval a c9627 := derived9627 a h
  have h8 : Entails.eval a c2101 := h 2100 (by decide)
  have h9 : Entails.eval a c2108 := h 2107 (by decide)
  have h10 : Entails.eval a c2444 := h 2443 (by decide)
  have h11 : Entails.eval a c2425 := h 2424 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9746 : DefaultClause 65 := directClause [(⟨54, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9746 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9690, some c9347, some c9743, some c8383, some c7994, some c9745, some c2481, some c2476, some c2484, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9746 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked9746 : lratChecker f9746 p9746 = .success := by decide +kernel
theorem unsat9746 : Unsatisfiable (PosFin 65) f9746 := by
  apply lratCheckerSound f9746 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9746
  · intro a ha; simp [p9746] at ha; subst a; trivial
  · exact checked9746
theorem derived9746 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9746 := by
  apply localUnsat_implies_entails f9746 [c9690, c9347, c9743, c8383, c7994, c9745, c2481, c2476, c2484] c9746 unsat9746 (by rfl) a
  have h0 : Entails.eval a c9690 := derived9690 a h
  have h1 : Entails.eval a c9347 := derived9347 a h
  have h2 : Entails.eval a c9743 := derived9743 a h
  have h3 : Entails.eval a c8383 := derived8383 a h
  have h4 : Entails.eval a c7994 := derived7994 a h
  have h5 : Entails.eval a c9745 := derived9745 a h
  have h6 : Entails.eval a c2481 := h 2480 (by decide)
  have h7 : Entails.eval a c2476 := h 2475 (by decide)
  have h8 : Entails.eval a c2484 := h 2483 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9747 : DefaultClause 65 := directClause [(⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9747 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9746, some c9690, some c9347, some c9743, some c8383, some c8269, some c7994, some c9627, some c2101, some c2104, some c2108, some c2115, some c2103, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9747 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9747 : lratChecker f9747 p9747 = .success := by decide +kernel
theorem unsat9747 : Unsatisfiable (PosFin 65) f9747 := by
  apply lratCheckerSound f9747 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9747
  · intro a ha; simp [p9747] at ha; subst a; trivial
  · exact checked9747
theorem derived9747 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9747 := by
  apply localUnsat_implies_entails f9747 [c9746, c9690, c9347, c9743, c8383, c8269, c7994, c9627, c2101, c2104, c2108, c2115, c2103] c9747 unsat9747 (by rfl) a
  have h0 : Entails.eval a c9746 := derived9746 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9347 := derived9347 a h
  have h3 : Entails.eval a c9743 := derived9743 a h
  have h4 : Entails.eval a c8383 := derived8383 a h
  have h5 : Entails.eval a c8269 := derived8269 a h
  have h6 : Entails.eval a c7994 := derived7994 a h
  have h7 : Entails.eval a c9627 := derived9627 a h
  have h8 : Entails.eval a c2101 := h 2100 (by decide)
  have h9 : Entails.eval a c2104 := h 2103 (by decide)
  have h10 : Entails.eval a c2108 := h 2107 (by decide)
  have h11 : Entails.eval a c2115 := h 2114 (by decide)
  have h12 : Entails.eval a c2103 := h 2102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9748 : DefaultClause 65 := directClause [(⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9748 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9347, some c9690, some c9743, some c7994, some c8269, some c8383, some c9747, some c2481, some c9416, some c2483, some c2476, some c1425, some c2428, some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p9748 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked9748 : lratChecker f9748 p9748 = .success := by decide +kernel
theorem unsat9748 : Unsatisfiable (PosFin 65) f9748 := by
  apply lratCheckerSound f9748 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9748
  · intro a ha; simp [p9748] at ha; subst a; trivial
  · exact checked9748
theorem derived9748 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9748 := by
  apply localUnsat_implies_entails f9748 [c9347, c9690, c9743, c7994, c8269, c8383, c9747, c2481, c9416, c2483, c2476, c1425, c2428] c9748 unsat9748 (by rfl) a
  have h0 : Entails.eval a c9347 := derived9347 a h
  have h1 : Entails.eval a c9690 := derived9690 a h
  have h2 : Entails.eval a c9743 := derived9743 a h
  have h3 : Entails.eval a c7994 := derived7994 a h
  have h4 : Entails.eval a c8269 := derived8269 a h
  have h5 : Entails.eval a c8383 := derived8383 a h
  have h6 : Entails.eval a c9747 := derived9747 a h
  have h7 : Entails.eval a c2481 := h 2480 (by decide)
  have h8 : Entails.eval a c9416 := derived9416 a h
  have h9 : Entails.eval a c2483 := h 2482 (by decide)
  have h10 : Entails.eval a c2476 := h 2475 (by decide)
  have h11 : Entails.eval a c1425 := h 1424 (by decide)
  have h12 : Entails.eval a c2428 := h 2427 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c9749 : DefaultClause 65 := directClause [(⟨7, by decide⟩, true), (⟨12, by decide⟩, true), (⟨61, by decide⟩, false), (⟨50, by decide⟩, true), (⟨9, by decide⟩, true), (⟨53, by decide⟩, true), (⟨54, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9749 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c4621, some c4642, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨61, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true))]
def p9749 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2]]
theorem checked9749 : lratChecker f9749 p9749 = .success := by decide +kernel
theorem unsat9749 : Unsatisfiable (PosFin 65) f9749 := by
  apply lratCheckerSound f9749 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9749
  · intro a ha; simp [p9749] at ha; subst a; trivial
  · exact checked9749
theorem derived9749 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9749 := by
  apply localUnsat_implies_entails f9749 [c4621, c4642] c9749 unsat9749 (by rfl) a
  have h0 : Entails.eval a c4621 := h 4620 (by decide)
  have h1 : Entails.eval a c4642 := h 4641 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c9750 : DefaultClause 65 := directClause [(⟨58, by decide⟩, true), (⟨7, by decide⟩, false), (⟨63, by decide⟩, true), (⟨51, by decide⟩, true), (⟨50, by decide⟩, true), (⟨53, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f9750 : DefaultFormula 65 := DefaultFormula.ofArray #[none, some c9748, some c3811, some c3618, some c2317, some (DefaultClause.unit (⟨58, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨63, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p9750 : List (Action (DefaultClause 65) (PosFin 65)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked9750 : lratChecker f9750 p9750 = .success := by decide +kernel
theorem unsat9750 : Unsatisfiable (PosFin 65) f9750 := by
  apply lratCheckerSound f9750 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p9750
  · intro a ha; simp [p9750] at ha; subst a; trivial
  · exact checked9750
theorem derived9750 (a : PosFin 65 → Bool) (h : InputSat a) : Entails.eval a c9750 := by
  apply localUnsat_implies_entails f9750 [c9748, c3811, c3618, c2317] c9750 unsat9750 (by rfl) a
  have h0 : Entails.eval a c9748 := derived9748 a h
  have h1 : Entails.eval a c3811 := h 3810 (by decide)
  have h2 : Entails.eval a c3618 := h 3617 (by decide)
  have h3 : Entails.eval a c2317 := h 2316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived9750

end CochromaticTwenty.Certificates.FixedCore0
