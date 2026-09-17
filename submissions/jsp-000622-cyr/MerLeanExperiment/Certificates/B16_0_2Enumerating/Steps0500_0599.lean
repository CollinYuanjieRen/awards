import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps0400_0499

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c914 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨32, by decide⟩, false), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c216, some c314, some c214, some c118, some c201, some c911, some c913, some c56, some c7, some c40, some c204, some c197, some c106, some c143, some c10, some c11, some c49, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p914 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 57) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c216, c314, c214, c118, c201, c911, c913, c56, c7, c40, c204, c197, c106, c143, c10, c11, c49] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c216 := h 215 (by decide)
  have h1 : Entails.eval a c314 := h 313 (by decide)
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c911 := derived911 a h
  have h6 : Entails.eval a c913 := derived913 a h
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c204 := h 203 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c10 := h 9 (by decide)
  have h15 : Entails.eval a c11 := h 10 (by decide)
  have h16 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, false), (⟨32, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c261, some c905, some c914, some c216, some c314, some c7, some c40, some c27, some c204, some c197, some c284, some c133, some c142, some c141, some c229, some c279, some c901, some c294, some c71, some c78, some c895, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p915 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 57) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c214, c261, c905, c914, c216, c314, c7, c40, c27, c204, c197, c284, c133, c142, c141, c229, c279, c901, c294, c71, c78, c895] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c905 := derived905 a h
  have h3 : Entails.eval a c914 := derived914 a h
  have h4 : Entails.eval a c216 := h 215 (by decide)
  have h5 : Entails.eval a c314 := h 313 (by decide)
  have h6 : Entails.eval a c7 := h 6 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c284 := h 283 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  have h14 : Entails.eval a c141 := h 140 (by decide)
  have h15 : Entails.eval a c229 := h 228 (by decide)
  have h16 : Entails.eval a c279 := h 278 (by decide)
  have h17 : Entails.eval a c901 := derived901 a h
  have h18 : Entails.eval a c294 := h 293 (by decide)
  have h19 : Entails.eval a c71 := h 70 (by decide)
  have h20 : Entails.eval a c78 := h 77 (by decide)
  have h21 : Entails.eval a c895 := derived895 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨13, by decide⟩, false), (⟨32, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c214, some c261, some c216, some c915, some c56, some c8, some c914, some c314, some c51, some c15, some c204, some c203, some c909, some c128, some c125, some c229, some c240, some c177, some c136, some c236, some c315, some c285, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p916 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 57) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c905, c214, c261, c216, c915, c56, c8, c914, c314, c51, c15, c204, c203, c909, c128, c125, c229, c240, c177, c136, c236, c315, c285] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c915 := derived915 a h
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c914 := derived914 a h
  have h8 : Entails.eval a c314 := h 313 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  have h13 : Entails.eval a c909 := derived909 a h
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c125 := h 124 (by decide)
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c177 := h 176 (by decide)
  have h19 : Entails.eval a c136 := h 135 (by decide)
  have h20 : Entails.eval a c236 := h 235 (by decide)
  have h21 : Entails.eval a c315 := h 314 (by decide)
  have h22 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c917 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨32, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c905, some c214, some c261, some c216, some c314, some c916, some c210, some c911, some c203, some c142, some c135, some c197, some c238, some c909, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p917 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 57) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c905, c214, c261, c216, c314, c916, c210, c911, c203, c142, c135, c197, c238, c909] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c216 := h 215 (by decide)
  have h4 : Entails.eval a c314 := h 313 (by decide)
  have h5 : Entails.eval a c916 := derived916 a h
  have h6 : Entails.eval a c210 := h 209 (by decide)
  have h7 : Entails.eval a c911 := derived911 a h
  have h8 : Entails.eval a c203 := h 202 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c238 := h 237 (by decide)
  have h13 : Entails.eval a c909 := derived909 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨41, by decide⟩, true), (⟨45, by decide⟩, false), (⟨25, by decide⟩, true), (⟨21, by decide⟩, false), (⟨30, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c210, some c286, some c238, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p918 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 57) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c210, c286, c238] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c210 := h 209 (by decide)
  have h1 : Entails.eval a c286 := h 285 (by decide)
  have h2 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨2, by decide⟩, true), (⟨4, by decide⟩, false), (⟨27, by decide⟩, false), (⟨41, by decide⟩, true), (⟨13, by decide⟩, true), (⟨25, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c144, some c315, some c287, some c88, some c12, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p919 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 57) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c137, c144, c315, c287, c88, c12] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  have h2 : Entails.eval a c315 := h 314 (by decide)
  have h3 : Entails.eval a c287 := h 286 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨40, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c66, some c106, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p920 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 57) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c71, c66, c106] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c66 := h 65 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c118, some c49, some c315, some c17, some c4, some c144, some c106, some c110, some c267, some c65, some c222, some c159, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p921 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 57) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c214, c118, c49, c315, c17, c4, c144, c106, c110, c267, c65, c222, c159] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c315 := h 314 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c4 := h 3 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true), (⟨6, by decide⟩, false), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c214, some c921, some c116, some c136, some c240, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p922 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 57) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c137, c214, c921, c116, c136, c240] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c214 := h 213 (by decide)
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c116 := h 115 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨41, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨32, by decide⟩, false), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c216, some c314, some c137, some c918, some c133, some c118, some c7, some c40, some c27, some c284, some c279, some c155, some c920, some c922, some c201, some c144, some c315, some c45, some c287, some c919, some c240, some c36, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p923 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 57) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c214, c216, c314, c137, c918, c133, c118, c7, c40, c27, c284, c279, c155, c920, c922, c201, c144, c315, c45, c287, c919, c240, c36] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c918 := derived918 a h
  have h5 : Entails.eval a c133 := h 132 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c279 := h 278 (by decide)
  have h12 : Entails.eval a c155 := h 154 (by decide)
  have h13 : Entails.eval a c920 := derived920 a h
  have h14 : Entails.eval a c922 := derived922 a h
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c315 := h 314 (by decide)
  have h18 : Entails.eval a c45 := h 44 (by decide)
  have h19 : Entails.eval a c287 := h 286 (by decide)
  have h20 : Entails.eval a c919 := derived919 a h
  have h21 : Entails.eval a c240 := h 239 (by decide)
  have h22 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true), (⟨17, by decide⟩, false), (⟨41, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c917, some c229, some c137, some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p924 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 57) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c214, c917, c229, c137] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c917 := derived917 a h
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨54, by decide⟩, true), (⟨55, by decide⟩, true), (⟨41, by decide⟩, false), (⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c79, some c105, some c365, some c78, some c38, some c102, some c34, some c98, some c254, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p925 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 57) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c79, c105, c365, c78, c38, c102, c34, c98, c254] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c365 := h 364 (by decide)
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c314, some c319, some c133, some c849, some c924, some c317, some c141, some c51, some c56, some c279, some c228, some c283, some c64, some c28, some c311, some c248, some c310, some c925, some c10, some c94, some c157, some c185, some c338, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p926 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 57) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c314, c319, c133, c849, c924, c317, c141, c51, c56, c279, c228, c283, c64, c28, c311, c248, c310, c925, c10, c94, c157, c185, c338] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c314 := h 313 (by decide)
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c133 := h 132 (by decide)
  have h3 : Entails.eval a c849 := derived849 a h
  have h4 : Entails.eval a c924 := derived924 a h
  have h5 : Entails.eval a c317 := h 316 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c279 := h 278 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c311 := h 310 (by decide)
  have h15 : Entails.eval a c248 := h 247 (by decide)
  have h16 : Entails.eval a c310 := h 309 (by decide)
  have h17 : Entails.eval a c925 := derived925 a h
  have h18 : Entails.eval a c10 := h 9 (by decide)
  have h19 : Entails.eval a c94 := h 93 (by decide)
  have h20 : Entails.eval a c157 := h 156 (by decide)
  have h21 : Entails.eval a c185 := h 184 (by decide)
  have h22 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, true), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c56, some c314, some c319, some c133, some c849, some c924, some c926, some c71, some c283, some c284, some c228, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p927 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 57) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c51, c56, c314, c319, c133, c849, c924, c926, c71, c283, c284, c228] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c849 := derived849 a h
  have h6 : Entails.eval a c924 := derived924 a h
  have h7 : Entails.eval a c926 := derived926 a h
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨23, by decide⟩, true), (⟨30, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c283, some c284, some c228, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p928 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 57) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c283, c284, c228] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c283 := h 282 (by decide)
  have h1 : Entails.eval a c284 := h 283 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, false), (⟨41, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c56, some c319, some c928, some c64, some c71, some c28, some c311, some c248, some c310, some c279, some c925, some c228, some c57, some c154, some c321, some c132, some c365, some c197, some c366, some c137, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p929 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 57) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c51, c56, c319, c928, c64, c71, c28, c311, c248, c310, c279, c925, c228, c57, c154, c321, c132, c365, c197, c366, c137] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c319 := h 318 (by decide)
  have h3 : Entails.eval a c928 := derived928 a h
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c311 := h 310 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c310 := h 309 (by decide)
  have h10 : Entails.eval a c279 := h 278 (by decide)
  have h11 : Entails.eval a c925 := derived925 a h
  have h12 : Entails.eval a c228 := h 227 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c154 := h 153 (by decide)
  have h15 : Entails.eval a c321 := h 320 (by decide)
  have h16 : Entails.eval a c132 := h 131 (by decide)
  have h17 : Entails.eval a c365 := h 364 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c366 := h 365 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨41, by decide⟩, false), (⟨30, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨27, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c51, some c56, some c314, some c319, some c929, some c261, some c263, some c231, some c117, some c39, some c208, some c28, some c8, some c35, some c885, some c105, some c264, some c283, some c284, some c198, some c156, some c455, some c37, some c26, some c226, some c180, some c66, some c57, some c53, some c109, some c89, some c352, some c162, some c247, some c181, some c184, some c116, some c65, some c361, some c345, some c364, some c99, some c160, some c377, some c328, some c134, some c389, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p930 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 57) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c317, c51, c56, c314, c319, c929, c261, c263, c231, c117, c39, c208, c28, c8, c35, c885, c105, c264, c283, c284, c198, c156, c455, c37, c26, c226, c180, c66, c57, c53, c109, c89, c352, c162, c247, c181, c184, c116, c65, c361, c345, c364, c99, c160, c377, c328, c134, c389] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c929 := derived929 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c231 := h 230 (by decide)
  have h9 : Entails.eval a c117 := h 116 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c8 := h 7 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c885 := derived885 a h
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c264 := h 263 (by decide)
  have h18 : Entails.eval a c283 := h 282 (by decide)
  have h19 : Entails.eval a c284 := h 283 (by decide)
  have h20 : Entails.eval a c198 := h 197 (by decide)
  have h21 : Entails.eval a c156 := h 155 (by decide)
  have h22 : Entails.eval a c455 := derived455 a h
  have h23 : Entails.eval a c37 := h 36 (by decide)
  have h24 : Entails.eval a c26 := h 25 (by decide)
  have h25 : Entails.eval a c226 := h 225 (by decide)
  have h26 : Entails.eval a c180 := h 179 (by decide)
  have h27 : Entails.eval a c66 := h 65 (by decide)
  have h28 : Entails.eval a c57 := h 56 (by decide)
  have h29 : Entails.eval a c53 := h 52 (by decide)
  have h30 : Entails.eval a c109 := h 108 (by decide)
  have h31 : Entails.eval a c89 := h 88 (by decide)
  have h32 : Entails.eval a c352 := h 351 (by decide)
  have h33 : Entails.eval a c162 := h 161 (by decide)
  have h34 : Entails.eval a c247 := h 246 (by decide)
  have h35 : Entails.eval a c181 := h 180 (by decide)
  have h36 : Entails.eval a c184 := h 183 (by decide)
  have h37 : Entails.eval a c116 := h 115 (by decide)
  have h38 : Entails.eval a c65 := h 64 (by decide)
  have h39 : Entails.eval a c361 := h 360 (by decide)
  have h40 : Entails.eval a c345 := h 344 (by decide)
  have h41 : Entails.eval a c364 := h 363 (by decide)
  have h42 : Entails.eval a c99 := h 98 (by decide)
  have h43 : Entails.eval a c160 := h 159 (by decide)
  have h44 : Entails.eval a c377 := h 376 (by decide)
  have h45 : Entails.eval a c328 := h 327 (by decide)
  have h46 : Entails.eval a c134 := h 133 (by decide)
  have h47 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c264, some c117, some c207, some c776, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p931 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 57) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c268, c264, c117, c207, c776] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c207 := h 206 (by decide)
  have h4 : Entails.eval a c776 := derived776 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨38, by decide⟩, true), (⟨8, by decide⟩, true), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c226, some c61, some c258, some c190, some c345, some c99, some c310, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p932 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 57) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c162, c226, c61, c258, c190, c345, c99, c310] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c226 := h 225 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c258 := h 257 (by decide)
  have h4 : Entails.eval a c190 := h 189 (by decide)
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨9, by decide⟩, false), (⟨7, by decide⟩, false), (⟨27, by decide⟩, false), (⟨38, by decide⟩, true), (⟨8, by decide⟩, true), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨31, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c26, some c317, some c314, some c930, some c205, some c931, some c3, some c30, some c79, some c105, some c78, some c932, some c19, some c198, some c199, some c180, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p933 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 57) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c319, c26, c317, c314, c930, c205, c931, c3, c30, c79, c105, c78, c932, c19, c198, c199, c180] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c930 := derived930 a h
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c931 := derived931 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c30 := h 29 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  have h12 : Entails.eval a c932 := derived932 a h
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  have h15 : Entails.eval a c199 := h 198 (by decide)
  have h16 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨39, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨9, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c55, some c317, some c313, some c319, some c933, some c578, some c144, some c285, some c180, some c200, some c370, some c176, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p934 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 57) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c26, c55, c317, c313, c319, c933, c578, c144, c285, c180, c200, c370, c176] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c319 := h 318 (by decide)
  have h5 : Entails.eval a c933 := derived933 a h
  have h6 : Entails.eval a c578 := derived578 a h
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c285 := h 284 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c370 := h 369 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c139, some c145, some c578, some c200, some c715, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p935 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 57) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c139, c145, c578, c200, c715] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c578 := derived578 a h
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c715 := derived715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c55, some c317, some c313, some c5, some c19, some c261, some c268, some c684, some c113, some c206, some c23, some c198, some c199, some c935, some c279, some c934, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p936 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 57) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c26, c55, c317, c313, c5, c19, c261, c268, c684, c113, c206, c23, c198, c199, c935, c279, c934] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c684 := derived684 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c198 := h 197 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c935 := derived935 a h
  have h15 : Entails.eval a c279 := h 278 (by decide)
  have h16 : Entails.eval a c934 := derived934 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c55, some c313, some c35, some c3, some c23, some c263, some c204, some c162, some c113, some c206, some c30, some c105, some c932, some c61, some c279, some c181, some c190, some c139, some c79, some c329, some c355, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p937 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 57) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c26, c55, c313, c35, c3, c23, c263, c204, c162, c113, c206, c30, c105, c932, c61, c279, c181, c190, c139, c79, c329, c355] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c162 := h 161 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c206 := h 205 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c932 := derived932 a h
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c279 := h 278 (by decide)
  have h16 : Entails.eval a c181 := h 180 (by decide)
  have h17 : Entails.eval a c190 := h 189 (by decide)
  have h18 : Entails.eval a c139 := h 138 (by decide)
  have h19 : Entails.eval a c79 := h 78 (by decide)
  have h20 : Entails.eval a c329 := h 328 (by decide)
  have h21 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨31, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c15, some c352, some c268, some c208, some c931, some c264, some c263, some c24, some c28, some c39, some c109, some c105, some c10, some c199, some c153, some c145, some c65, some c160, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p938 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 57) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c162, c15, c352, c268, c208, c931, c264, c263, c24, c28, c39, c109, c105, c10, c199, c153, c145, c65, c160] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c352 := h 351 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c208 := h 207 (by decide)
  have h5 : Entails.eval a c931 := derived931 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c10 := h 9 (by decide)
  have h14 : Entails.eval a c199 := h 198 (by decide)
  have h15 : Entails.eval a c153 := h 152 (by decide)
  have h16 : Entails.eval a c145 := h 144 (by decide)
  have h17 : Entails.eval a c65 := h 64 (by decide)
  have h18 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c15, some c938, some c278, some c142, some c135, some c199, some c239, some c139, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p939 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 57) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c162, c15, c938, c278, c142, c135, c199, c239, c139] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c938 := derived938 a h
  have h3 : Entails.eval a c278 := h 277 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c239 := h 238 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨14, by decide⟩, true), (⟨9, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c263, some c205, some c777, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p940 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 57) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c268, c263, c205, c777] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c777 := derived777 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨31, by decide⟩, false), (⟨16, by decide⟩, false), (⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c268, some c142, some c135, some c198, some c328, some c940, some c39, some c54, some c208, some c288, some c233, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p941 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 57) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c162, c268, c142, c135, c198, c328, c940, c39, c54, c208, c288, c233] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c328 := h 327 (by decide)
  have h6 : Entails.eval a c940 := derived940 a h
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c208 := h 207 (by decide)
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨37, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c55, some c317, some c313, some c352, some c162, some c15, some c939, some c941, some c278, some c208, some c931, some c264, some c263, some c776, some c24, some c28, some c39, some c109, some c105, some c10, some c153, some c930, some c65, some c57, some c285, some c287, some c327, some c181, some c184, some c88, some c364, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p942 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 57) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c268, c55, c317, c313, c352, c162, c15, c939, c941, c278, c208, c931, c264, c263, c776, c24, c28, c39, c109, c105, c10, c153, c930, c65, c57, c285, c287, c327, c181, c184, c88, c364] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c352 := h 351 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c939 := derived939 a h
  have h8 : Entails.eval a c941 := derived941 a h
  have h9 : Entails.eval a c278 := h 277 (by decide)
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c931 := derived931 a h
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c263 := h 262 (by decide)
  have h14 : Entails.eval a c776 := derived776 a h
  have h15 : Entails.eval a c24 := h 23 (by decide)
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c39 := h 38 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c10 := h 9 (by decide)
  have h21 : Entails.eval a c153 := h 152 (by decide)
  have h22 : Entails.eval a c930 := derived930 a h
  have h23 : Entails.eval a c65 := h 64 (by decide)
  have h24 : Entails.eval a c57 := h 56 (by decide)
  have h25 : Entails.eval a c285 := h 284 (by decide)
  have h26 : Entails.eval a c287 := h 286 (by decide)
  have h27 : Entails.eval a c327 := h 326 (by decide)
  have h28 : Entails.eval a c181 := h 180 (by decide)
  have h29 : Entails.eval a c184 := h 183 (by decide)
  have h30 : Entails.eval a c88 := h 87 (by decide)
  have h31 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨16, by decide⟩, false), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c153, some c198, some c66, some c940, some c105, some c39, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p943 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 57) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c268, c153, c198, c66, c940, c105, c39] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c153 := h 152 (by decide)
  have h2 : Entails.eval a c198 := h 197 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c940 := derived940 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨35, by decide⟩, true), (⟨37, by decide⟩, false), (⟨19, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c15, some c943, some c113, some c10, some c263, some c105, some c39, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p944 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 57) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c268, c15, c943, c113, c10, c263, c105, c39] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c943 := derived943 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c10 := h 9 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c113, some c143, some c263, some c53, some c39, some c11, some c105, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p945 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 57) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c113, c143, c263, c53, c39, c11, c105] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c113 := h 112 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, false), (⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c55, some c317, some c313, some c937, some c268, some c226, some c942, some c59, some c944, some c203, some c190, some c945, some c153, some c943, some c66, some c8, some c17, some c105, some c263, some c109, some c103, some c96, some c205, some c252, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p946 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 57) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c26, c55, c317, c313, c937, c268, c226, c942, c59, c944, c203, c190, c945, c153, c943, c66, c8, c17, c105, c263, c109, c103, c96, c205, c252] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c942 := derived942 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c944 := derived944 a h
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c190 := h 189 (by decide)
  have h12 : Entails.eval a c945 := derived945 a h
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c943 := derived943 a h
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c8 := h 7 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c105 := h 104 (by decide)
  have h19 : Entails.eval a c263 := h 262 (by decide)
  have h20 : Entails.eval a c109 := h 108 (by decide)
  have h21 : Entails.eval a c103 := h 102 (by decide)
  have h22 : Entails.eval a c96 := h 95 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨19, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c205, some c264, some c207, some c31, some c53, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p947 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 57) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c205, c264, c207, c31, c53] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c205 := h 204 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨6, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c5, some c130, some c105, some c947, some c263, some c8, some c202, some c198, some c141, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p948 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 57) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c268, c5, c130, c105, c947, c263, c8, c202, c198, c141] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c130 := h 129 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c947 := derived947 a h
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨8, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c112, some c30, some c35, some c263, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p949 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 57) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c105, c112, c30, c35, c263] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨7, by decide⟩, false), (⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c55, some c317, some c313, some c948, some c949, some c936, some c5, some c19, some c261, some c684, some c113, some c206, some c199, some c51, some c935, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p950 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 57) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c26, c55, c317, c313, c948, c949, c936, c5, c19, c261, c684, c113, c206, c199, c51, c935] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c317 := h 316 (by decide)
  have h3 : Entails.eval a c313 := h 312 (by decide)
  have h4 : Entails.eval a c948 := derived948 a h
  have h5 : Entails.eval a c949 := derived949 a h
  have h6 : Entails.eval a c936 := derived936 a h
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c684 := derived684 a h
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c51 := h 50 (by decide)
  have h15 : Entails.eval a c935 := derived935 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨21, by decide⟩, false), (⟨35, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c162, some c203, some c699, some c61, some c49, some c277, some c4, some c60, some c256, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p951 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 57) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c162, c203, c699, c61, c49, c277, c4, c60, c256] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c699 := derived699 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c277 := h 276 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨43, by decide⟩, true), (⟨47, by decide⟩, false), (⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c684, some c8, some c175, some c244, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p952 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 57) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c684, c8, c175, c244] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c684 := derived684 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c175 := h 174 (by decide)
  have h3 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨11, by decide⟩, false), (⟨31, by decide⟩, true), (⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c222, some c162, some c951, some c226, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p953 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 57) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c222, c162, c951, c226] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c222 := h 221 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c951 := derived951 a h
  have h3 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c113, some c197, some c206, some c51, some c139, some c87, some c952, some c699, some c953, some c49, some c281, some c283, some c73, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p954 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 57) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c313, c113, c197, c206, c51, c139, c87, c952, c699, c953, c49, c281, c283, c73] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c952 := derived952 a h
  have h8 : Entails.eval a c699 := derived699 a h
  have h9 : Entails.eval a c953 := derived953 a h
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c283 := h 282 (by decide)
  have h13 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c954, some c946, some c3, some c23, some c283, some c162, some c75, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p955 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 57) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c954, c946, c3, c23, c283, c162, c75] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c954 := derived954 a h
  have h1 : Entails.eval a c946 := derived946 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c283 := h 282 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c317, some c313, some c113, some c206, some c205, some c955, some c950, some c19, some c283, some c684, some c199, some c64, some c28, some c75, some c935, some c260, some c252, some c51, some c319, some c23, some c144, some c353, some c157, some c338, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p956 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 57) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c317, c313, c113, c206, c205, c955, c950, c19, c283, c684, c199, c64, c28, c75, c935, c260, c252, c51, c319, c23, c144, c353, c157, c338] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c317 := h 316 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c206 := h 205 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c955 := derived955 a h
  have h6 : Entails.eval a c950 := derived950 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c283 := h 282 (by decide)
  have h9 : Entails.eval a c684 := derived684 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c935 := derived935 a h
  have h15 : Entails.eval a c260 := h 259 (by decide)
  have h16 : Entails.eval a c252 := h 251 (by decide)
  have h17 : Entails.eval a c51 := h 50 (by decide)
  have h18 : Entails.eval a c319 := h 318 (by decide)
  have h19 : Entails.eval a c23 := h 22 (by decide)
  have h20 : Entails.eval a c144 := h 143 (by decide)
  have h21 : Entails.eval a c353 := h 352 (by decide)
  have h22 : Entails.eval a c157 := h 156 (by decide)
  have h23 : Entails.eval a c338 := h 337 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c956, some c261, some c263, some c39, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p957 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 57) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c956, c261, c263, c39] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c956 := derived956 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c313, some c957, some c55, some c107, some c6, some c26, some c38, some c261, some c113, some c21, some c154, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p958 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 57) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c313, c957, c55, c107, c6, c26, c38, c261, c113, c21, c154] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c313 := h 312 (by decide)
  have h1 : Entails.eval a c957 := derived957 a h
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨32, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c958, some c112, some c949, some c34, some c55, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true))]
def p959 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 57) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c958, c112, c949, c34, c55] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c949 := derived949 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨37, by decide⟩, false), (⟨24, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, false), (⟨31, by decide⟩, true), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c112, some c105, some c154, some c198, some c885, some c66, some c131, some c139, some c162, some c92, some c239, some c175, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p960 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 57) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c268, c112, c105, c154, c198, c885, c66, c131, c139, c162, c92, c239, c175] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  have h4 : Entails.eval a c198 := h 197 (by decide)
  have h5 : Entails.eval a c885 := derived885 a h
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c239 := h 238 (by decide)
  have h12 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true), (⟨31, by decide⟩, true), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c112, some c105, some c227, some c960, some c141, some c727, some c10, some c202, some c139, some c131, some c204, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p961 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 57) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c268, c112, c105, c227, c960, c141, c727, c10, c202, c139, c131, c204] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c227 := h 226 (by decide)
  have h4 : Entails.eval a c960 := derived960 a h
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c727 := derived727 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  have h10 : Entails.eval a c131 := h 130 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨32, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c56, some c105, some c313, some c317, some c55, some c6, some c26, some c283, some c961, some c263, some c113, some c21, some c154, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p962 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 57) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c56, c105, c313, c317, c55, c6, c26, c283, c961, c263, c113, c21, c154] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c56 := h 55 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c317 := h 316 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c961 := derived961 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c21, some c154, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p963 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 57) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c1, c21, c154] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨38, by decide⟩, false), (⟨6, by decide⟩, true), (⟨14, by decide⟩, false), (⟨31, by decide⟩, true), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c963, some c263, some c268, some c112, some c154, some c198, some c960, some c57, some c131, some c227, some c182, some c181, some c351, some c98, some c337, some c220, some c249, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p964 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 57) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c105, c963, c263, c268, c112, c154, c198, c960, c57, c131, c227, c182, c181, c351, c98, c337, c220, c249] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c154 := h 153 (by decide)
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c960 := derived960 a h
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c182 := h 181 (by decide)
  have h12 : Entails.eval a c181 := h 180 (by decide)
  have h13 : Entails.eval a c351 := h 350 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  have h15 : Entails.eval a c337 := h 336 (by decide)
  have h16 : Entails.eval a c220 := h 219 (by decide)
  have h17 : Entails.eval a c249 := h 248 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨11, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨31, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c699, some c11, some c52, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p965 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 57) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c203, c699, c11, c52] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c699 := derived699 a h
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c966 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨32, by decide⟩, false), (⟨8, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f966 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c962, some c214, some c118, some c56, some c112, some c105, some c26, some c963, some c263, some c964, some c10, some c965, some c131, some c167, some c202, some c227, some c124, some c264, some c225, some c165, some c280, some c116, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p966 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked966 : lratChecker f966 p966 = .success := by decide +kernel
theorem unsat966 : Unsatisfiable (PosFin 57) f966 := by
  apply lratCheckerSound f966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p966
  · intro a ha; simp [p966] at ha; subst a; trivial
  · exact checked966
theorem derived966 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c966 := by
  apply localUnsat_implies_entails f966 [c268, c962, c214, c118, c56, c112, c105, c26, c963, c263, c964, c10, c965, c131, c167, c202, c227, c124, c264, c225, c165, c280, c116] c966 unsat966 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c962 := derived962 a h
  have h2 : Entails.eval a c214 := h 213 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c963 := derived963 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c964 := derived964 a h
  have h11 : Entails.eval a c10 := h 9 (by decide)
  have h12 : Entails.eval a c965 := derived965 a h
  have h13 : Entails.eval a c131 := h 130 (by decide)
  have h14 : Entails.eval a c167 := h 166 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c227 := h 226 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c264 := h 263 (by decide)
  have h19 : Entails.eval a c225 := h 224 (by decide)
  have h20 : Entails.eval a c165 := h 164 (by decide)
  have h21 : Entails.eval a c280 := h 279 (by decide)
  have h22 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c967 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f967 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c165, some c67, some c73, some c347, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p967 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked967 : lratChecker f967 p967 = .success := by decide +kernel
theorem unsat967 : Unsatisfiable (PosFin 57) f967 := by
  apply lratCheckerSound f967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p967
  · intro a ha; simp [p967] at ha; subst a; trivial
  · exact checked967
theorem derived967 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c967 := by
  apply localUnsat_implies_entails f967 [c11, c165, c67, c73, c347] c967 unsat967 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c165 := h 164 (by decide)
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c73 := h 72 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c968 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨14, by decide⟩, false), (⟨9, by decide⟩, true), (⟨38, by decide⟩, false), (⟨6, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f968 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c967, some c109, some c9, some c159, some c65, some c22, some c58, some c347, some c252, some c64, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p968 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked968 : lratChecker f968 p968 = .success := by decide +kernel
theorem unsat968 : Unsatisfiable (PosFin 57) f968 := by
  apply lratCheckerSound f968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p968
  · intro a ha; simp [p968] at ha; subst a; trivial
  · exact checked968
theorem derived968 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c968 := by
  apply localUnsat_implies_entails f968 [c967, c109, c9, c159, c65, c22, c58, c347, c252, c64] c968 unsat968 (by rfl) a
  have h0 : Entails.eval a c967 := derived967 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c159 := h 158 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c347 := h 346 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c969 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f969 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c128, some c116, some c163, some c53, some c224, some c210, some c277, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p969 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked969 : lratChecker f969 p969 = .success := by decide +kernel
theorem unsat969 : Unsatisfiable (PosFin 57) f969 := by
  apply lratCheckerSound f969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p969
  · intro a ha; simp [p969] at ha; subst a; trivial
  · exact checked969
theorem derived969 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c969 := by
  apply localUnsat_implies_entails f969 [c128, c116, c163, c53, c224, c210, c277] c969 unsat969 (by rfl) a
  have h0 : Entails.eval a c128 := h 127 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c163 := h 162 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c970 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨36, by decide⟩, false), (⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨35, by decide⟩, false), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f970 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c277, some c210, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p970 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked970 : lratChecker f970 p970 = .success := by decide +kernel
theorem unsat970 : Unsatisfiable (PosFin 57) f970 := by
  apply lratCheckerSound f970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p970
  · intro a ha; simp [p970] at ha; subst a; trivial
  · exact checked970
theorem derived970 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c970 := by
  apply localUnsat_implies_entails f970 [c53, c277, c210] c970 unsat970 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c971 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨19, by decide⟩, true), (⟨35, by decide⟩, false), (⟨40, by decide⟩, true), (⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, false), (⟨16, by decide⟩, true), (⟨12, by decide⟩, true), (⟨8, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f971 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c263, some c252, some c969, some c250, some c342, some c970, some c149, some c56, some c55, some c216, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p971 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked971 : lratChecker f971 p971 = .success := by decide +kernel
theorem unsat971 : Unsatisfiable (PosFin 57) f971 := by
  apply lratCheckerSound f971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p971
  · intro a ha; simp [p971] at ha; subst a; trivial
  · exact checked971
theorem derived971 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c971 := by
  apply localUnsat_implies_entails f971 [c262, c263, c252, c969, c250, c342, c970, c149, c56, c55, c216] c971 unsat971 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c263 := h 262 (by decide)
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c969 := derived969 a h
  have h4 : Entails.eval a c250 := h 249 (by decide)
  have h5 : Entails.eval a c342 := h 341 (by decide)
  have h6 : Entails.eval a c970 := derived970 a h
  have h7 : Entails.eval a c149 := h 148 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c972 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨40, by decide⟩, true), (⟨18, by decide⟩, false), (⟨10, by decide⟩, false), (⟨8, by decide⟩, false), (⟨14, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f972 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c202, some c896, some c120, some c265, some c56, some c55, some c216, some c261, some c131, some c227, some c162, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p972 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked972 : lratChecker f972 p972 = .success := by decide +kernel
theorem unsat972 : Unsatisfiable (PosFin 57) f972 := by
  apply lratCheckerSound f972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p972
  · intro a ha; simp [p972] at ha; subst a; trivial
  · exact checked972
theorem derived972 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c972 := by
  apply localUnsat_implies_entails f972 [c202, c896, c120, c265, c56, c55, c216, c261, c131, c227, c162] c972 unsat972 (by rfl) a
  have h0 : Entails.eval a c202 := h 201 (by decide)
  have h1 : Entails.eval a c896 := derived896 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  have h9 : Entails.eval a c227 := h 226 (by decide)
  have h10 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c973 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨38, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f973 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c347, some c351, some c65, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p973 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked973 : lratChecker f973 p973 = .success := by decide +kernel
theorem unsat973 : Unsatisfiable (PosFin 57) f973 := by
  apply lratCheckerSound f973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p973
  · intro a ha; simp [p973] at ha; subst a; trivial
  · exact checked973
theorem derived973 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c973 := by
  apply localUnsat_implies_entails f973 [c347, c351, c65] c973 unsat973 (by rfl) a
  have h0 : Entails.eval a c347 := h 346 (by decide)
  have h1 : Entails.eval a c351 := h 350 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c974 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨40, by decide⟩, true), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f974 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c22, some c58, some c264, some c185, some c225, some c129, some c59, some c94, some c352, some c188, some c227, some c344, some c245, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p974 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked974 : lratChecker f974 p974 = .success := by decide +kernel
theorem unsat974 : Unsatisfiable (PosFin 57) f974 := by
  apply lratCheckerSound f974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p974
  · intro a ha; simp [p974] at ha; subst a; trivial
  · exact checked974
theorem derived974 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c974 := by
  apply localUnsat_implies_entails f974 [c200, c22, c58, c264, c185, c225, c129, c59, c94, c352, c188, c227, c344, c245] c974 unsat974 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c264 := h 263 (by decide)
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c225 := h 224 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c352 := h 351 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c227 := h 226 (by decide)
  have h12 : Entails.eval a c344 := h 343 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c975 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨11, by decide⟩, false), (⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨2, by decide⟩, true), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f975 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c973, some c974, some c350, some c157, some c225, some c59, some c920, some c267, some c185, some c253, some c227, some c342, some c346, some c631, some c341, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p975 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked975 : lratChecker f975 p975 = .success := by decide +kernel
theorem unsat975 : Unsatisfiable (PosFin 57) f975 := by
  apply lratCheckerSound f975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p975
  · intro a ha; simp [p975] at ha; subst a; trivial
  · exact checked975
theorem derived975 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c975 := by
  apply localUnsat_implies_entails f975 [c973, c974, c350, c157, c225, c59, c920, c267, c185, c253, c227, c342, c346, c631, c341] c975 unsat975 (by rfl) a
  have h0 : Entails.eval a c973 := derived973 a h
  have h1 : Entails.eval a c974 := derived974 a h
  have h2 : Entails.eval a c350 := h 349 (by decide)
  have h3 : Entails.eval a c157 := h 156 (by decide)
  have h4 : Entails.eval a c225 := h 224 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c920 := derived920 a h
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c185 := h 184 (by decide)
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c227 := h 226 (by decide)
  have h11 : Entails.eval a c342 := h 341 (by decide)
  have h12 : Entails.eval a c346 := h 345 (by decide)
  have h13 : Entails.eval a c631 := derived631 a h
  have h14 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c976 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨39, by decide⟩, true), (⟨52, by decide⟩, true), (⟨50, by decide⟩, true), (⟨40, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f976 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c342, some c341, some c631, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p976 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked976 : lratChecker f976 p976 = .success := by decide +kernel
theorem unsat976 : Unsatisfiable (PosFin 57) f976 := by
  apply lratCheckerSound f976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p976
  · intro a ha; simp [p976] at ha; subst a; trivial
  · exact checked976
theorem derived976 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c976 := by
  apply localUnsat_implies_entails f976 [c342, c341, c631] c976 unsat976 (by rfl) a
  have h0 : Entails.eval a c342 := h 341 (by decide)
  have h1 : Entails.eval a c341 := h 340 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c977 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨54, by decide⟩, false), (⟨49, by decide⟩, false), (⟨12, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f977 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c53, some c298, some c143, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p977 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked977 : lratChecker f977 p977 = .success := by decide +kernel
theorem unsat977 : Unsatisfiable (PosFin 57) f977 := by
  apply lratCheckerSound f977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p977
  · intro a ha; simp [p977] at ha; subst a; trivial
  · exact checked977
theorem derived977 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c977 := by
  apply localUnsat_implies_entails f977 [c53, c298, c143] c977 unsat977 (by rfl) a
  have h0 : Entails.eval a c53 := h 52 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c978 : DefaultClause 57 := directClause [(⟨55, by decide⟩, true), (⟨39, by decide⟩, true), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨49, by decide⟩, false), (⟨50, by decide⟩, true), (⟨11, by decide⟩, false), (⟨10, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨38, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f978 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c109, some c97, some c345, some c246, some c977, some c118, some c214, some c202, some c54, some c52, some c131, some c699, some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p978 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked978 : lratChecker f978 p978 = .success := by decide +kernel
theorem unsat978 : Unsatisfiable (PosFin 57) f978 := by
  apply lratCheckerSound f978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p978
  · intro a ha; simp [p978] at ha; subst a; trivial
  · exact checked978
theorem derived978 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c978 := by
  apply localUnsat_implies_entails f978 [c200, c109, c97, c345, c246, c977, c118, c214, c202, c54, c52, c131, c699] c978 unsat978 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c977 := derived977 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c214 := h 213 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c52 := h 51 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c699 := derived699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c979 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨33, by decide⟩, false), (⟨51, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨40, by decide⟩, true), (⟨38, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f979 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c28, some c185, some c472, some c109, some c267, some c264, some c227, some c32, some c346, some c978, some c255, some c191, some c874, some c228, some c873, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p979 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked979 : lratChecker f979 p979 = .success := by decide +kernel
theorem unsat979 : Unsatisfiable (PosFin 57) f979 := by
  apply lratCheckerSound f979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p979
  · intro a ha; simp [p979] at ha; subst a; trivial
  · exact checked979
theorem derived979 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c979 := by
  apply localUnsat_implies_entails f979 [c28, c185, c472, c109, c267, c264, c227, c32, c346, c978, c255, c191, c874, c228, c873] c979 unsat979 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c185 := h 184 (by decide)
  have h2 : Entails.eval a c472 := derived472 a h
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c227 := h 226 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c346 := h 345 (by decide)
  have h9 : Entails.eval a c978 := derived978 a h
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c874 := derived874 a h
  have h13 : Entails.eval a c228 := h 227 (by decide)
  have h14 : Entails.eval a c873 := derived873 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c980 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f980 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c123, some c896, some c116, some c53, some c138, some c230, some c89, some c171, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p980 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked980 : lratChecker f980 p980 = .success := by decide +kernel
theorem unsat980 : Unsatisfiable (PosFin 57) f980 := by
  apply lratCheckerSound f980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p980
  · intro a ha; simp [p980] at ha; subst a; trivial
  · exact checked980
theorem derived980 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c980 := by
  apply localUnsat_implies_entails f980 [c123, c896, c116, c53, c138, c230, c89, c171] c980 unsat980 (by rfl) a
  have h0 : Entails.eval a c123 := h 122 (by decide)
  have h1 : Entails.eval a c896 := derived896 a h
  have h2 : Entails.eval a c116 := h 115 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c230 := h 229 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c981 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨19, by decide⟩, false), (⟨33, by decide⟩, false), (⟨51, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨38, by decide⟩, true), (⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f981 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c267, some c264, some c32, some c185, some c58, some c979, some c160, some c348, some c8, some c120, some c131, some c472, some c204, some c978, some c874, some c255, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p981 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked981 : lratChecker f981 p981 = .success := by decide +kernel
theorem unsat981 : Unsatisfiable (PosFin 57) f981 := by
  apply lratCheckerSound f981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p981
  · intro a ha; simp [p981] at ha; subst a; trivial
  · exact checked981
theorem derived981 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c981 := by
  apply localUnsat_implies_entails f981 [c109, c267, c264, c32, c185, c58, c979, c160, c348, c8, c120, c131, c472, c204, c978, c874, c255] c981 unsat981 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c979 := derived979 a h
  have h7 : Entails.eval a c160 := h 159 (by decide)
  have h8 : Entails.eval a c348 := h 347 (by decide)
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c472 := derived472 a h
  have h13 : Entails.eval a c204 := h 203 (by decide)
  have h14 : Entails.eval a c978 := derived978 a h
  have h15 : Entails.eval a c874 := derived874 a h
  have h16 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c982 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨34, by decide⟩, false), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f982 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c28, some c8, some c160, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p982 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked982 : lratChecker f982 p982 = .success := by decide +kernel
theorem unsat982 : Unsatisfiable (PosFin 57) f982 := by
  apply lratCheckerSound f982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p982
  · intro a ha; simp [p982] at ha; subst a; trivial
  · exact checked982
theorem derived982 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c982 := by
  apply localUnsat_implies_entails f982 [c28, c8, c160] c982 unsat982 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c983 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨33, by decide⟩, false), (⟨30, by decide⟩, true), (⟨25, by decide⟩, false), (⟨34, by decide⟩, false), (⟨22, by decide⟩, false), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f983 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c982, some c259, some c187, some c64, some c138, some c160, some c272, some c243, some c140, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p983 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked983 : lratChecker f983 p983 = .success := by decide +kernel
theorem unsat983 : Unsatisfiable (PosFin 57) f983 := by
  apply lratCheckerSound f983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p983
  · intro a ha; simp [p983] at ha; subst a; trivial
  · exact checked983
theorem derived983 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c983 := by
  apply localUnsat_implies_entails f983 [c982, c259, c187, c64, c138, c160, c272, c243, c140] c983 unsat983 (by rfl) a
  have h0 : Entails.eval a c982 := derived982 a h
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c187 := h 186 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c243 := h 242 (by decide)
  have h8 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c984 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f984 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c185, some c200, some c265, some c22, some c157, some c982, some c59, some c262, some c111, some c113, some c32, some c42, some c267, some c218, some c983, some c339, some c159, some c138, some c321, some c89, some c171, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p984 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked984 : lratChecker f984 p984 = .success := by decide +kernel
theorem unsat984 : Unsatisfiable (PosFin 57) f984 := by
  apply lratCheckerSound f984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p984
  · intro a ha; simp [p984] at ha; subst a; trivial
  · exact checked984
theorem derived984 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c984 := by
  apply localUnsat_implies_entails f984 [c185, c200, c265, c22, c157, c982, c59, c262, c111, c113, c32, c42, c267, c218, c983, c339, c159, c138, c321, c89, c171] c984 unsat984 (by rfl) a
  have h0 : Entails.eval a c185 := h 184 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c265 := h 264 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c982 := derived982 a h
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c983 := derived983 a h
  have h15 : Entails.eval a c339 := h 338 (by decide)
  have h16 : Entails.eval a c159 := h 158 (by decide)
  have h17 : Entails.eval a c138 := h 137 (by decide)
  have h18 : Entails.eval a c321 := h 320 (by decide)
  have h19 : Entails.eval a c89 := h 88 (by decide)
  have h20 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c985 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨9, by decide⟩, true), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨50, by decide⟩, false), (⟨6, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f985 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c984, some c123, some c980, some c262, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p985 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked985 : lratChecker f985 p985 = .success := by decide +kernel
theorem unsat985 : Unsatisfiable (PosFin 57) f985 := by
  apply lratCheckerSound f985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p985
  · intro a ha; simp [p985] at ha; subst a; trivial
  · exact checked985
theorem derived985 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c985 := by
  apply localUnsat_implies_entails f985 [c200, c984, c123, c980, c262] c985 unsat985 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c984 := derived984 a h
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c980 := derived980 a h
  have h4 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c986 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true), (⟨16, by decide⟩, true), (⟨41, by decide⟩, true), (⟨23, by decide⟩, true), (⟨30, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f986 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c923, some c151, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p986 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked986 : lratChecker f986 p986 = .success := by decide +kernel
theorem unsat986 : Unsatisfiable (PosFin 57) f986 := by
  apply lratCheckerSound f986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p986
  · intro a ha; simp [p986] at ha; subst a; trivial
  · exact checked986
theorem derived986 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c986 := by
  apply localUnsat_implies_entails f986 [c923, c151] c986 unsat986 (by rfl) a
  have h0 : Entails.eval a c923 := derived923 a h
  have h1 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c987 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f987 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c318, some c208, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p987 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked987 : lratChecker f987 p987 = .success := by decide +kernel
theorem unsat987 : Unsatisfiable (PosFin 57) f987 := by
  apply lratCheckerSound f987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p987
  · intro a ha; simp [p987] at ha; subst a; trivial
  · exact checked987
theorem derived987 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c987 := by
  apply localUnsat_implies_entails f987 [c316, c318, c208] c987 unsat987 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c318 := h 317 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c988 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨19, by decide⟩, false), (⟨29, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f988 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c113, some c212, some c268, some c263, some c727, some c213, some c292, some c55, some c884, some c37, some c89, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p988 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked988 : lratChecker f988 p988 = .success := by decide +kernel
theorem unsat988 : Unsatisfiable (PosFin 57) f988 := by
  apply lratCheckerSound f988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p988
  · intro a ha; simp [p988] at ha; subst a; trivial
  · exact checked988
theorem derived988 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c988 := by
  apply localUnsat_implies_entails f988 [c133, c113, c212, c268, c263, c727, c213, c292, c55, c884, c37, c89] c988 unsat988 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c727 := derived727 a h
  have h6 : Entails.eval a c213 := h 212 (by decide)
  have h7 : Entails.eval a c292 := h 291 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c884 := derived884 a h
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c989 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, false), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c142, some c200, some c203, some c818, some c2, some c47, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p989 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 57) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c319, c142, c200, c203, c818, c2, c47] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c203 := h 202 (by decide)
  have h4 : Entails.eval a c818 := derived818 a h
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c990 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f990 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c113, some c118, some c6, some c989, some c212, some c988, some c261, some c126, some c130, some c699, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p990 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked990 : lratChecker f990 p990 = .success := by decide +kernel
theorem unsat990 : Unsatisfiable (PosFin 57) f990 := by
  apply lratCheckerSound f990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p990
  · intro a ha; simp [p990] at ha; subst a; trivial
  · exact checked990
theorem derived990 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c990 := by
  apply localUnsat_implies_entails f990 [c116, c113, c118, c6, c989, c212, c988, c261, c126, c130, c699] c990 unsat990 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c989 := derived989 a h
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c988 := derived988 a h
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c130 := h 129 (by decide)
  have h10 : Entails.eval a c699 := derived699 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c991 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f991 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c2, some c114, some c759, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p991 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked991 : lratChecker f991 p991 = .success := by decide +kernel
theorem unsat991 : Unsatisfiable (PosFin 57) f991 := by
  apply lratCheckerSound f991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p991
  · intro a ha; simp [p991] at ha; subst a; trivial
  · exact checked991
theorem derived991 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c991 := by
  apply localUnsat_implies_entails f991 [c2, c114, c759] c991 unsat991 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c114 := h 113 (by decide)
  have h2 : Entails.eval a c759 := derived759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c992 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨29, by decide⟩, true), (⟨28, by decide⟩, true), (⟨41, by decide⟩, false), (⟨17, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f992 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c317, some c47, some c213, some c22, some c232, some c158, some c293, some c295, some c24, some c229, some c88, some c32, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p992 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked992 : lratChecker f992 p992 = .success := by decide +kernel
theorem unsat992 : Unsatisfiable (PosFin 57) f992 := by
  apply lratCheckerSound f992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p992
  · intro a ha; simp [p992] at ha; subst a; trivial
  · exact checked992
theorem derived992 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c992 := by
  apply localUnsat_implies_entails f992 [c116, c317, c47, c213, c22, c232, c158, c293, c295, c24, c229, c88, c32] c992 unsat992 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c232 := h 231 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c295 := h 294 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c993 : DefaultClause 57 := directClause [(⟨32, by decide⟩, true), (⟨45, by decide⟩, true), (⟨29, by decide⟩, true), (⟨28, by decide⟩, true), (⟨41, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f993 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c213, some c295, some c232, some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p993 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked993 : lratChecker f993 p993 = .success := by decide +kernel
theorem unsat993 : Unsatisfiable (PosFin 57) f993 := by
  apply lratCheckerSound f993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p993
  · intro a ha; simp [p993] at ha; subst a; trivial
  · exact checked993
theorem derived993 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c993 := by
  apply localUnsat_implies_entails f993 [c213, c295, c232] c993 unsat993 (by rfl) a
  have h0 : Entails.eval a c213 := h 212 (by decide)
  have h1 : Entails.eval a c295 := h 294 (by decide)
  have h2 : Entails.eval a c232 := h 231 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c994 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c133, some c113, some c991, some c118, some c6, some c116, some c990, some c200, some c142, some c992, some c208, some c261, some c229, some c212, some c993, some c927, some c33, some c36, some c109, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p994 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 57) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c133, c113, c991, c118, c6, c116, c990, c200, c142, c992, c208, c261, c229, c212, c993, c927, c33, c36, c109] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c133 := h 132 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c991 := derived991 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c990 := derived990 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c142 := h 141 (by decide)
  have h9 : Entails.eval a c992 := derived992 a h
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c261 := h 260 (by decide)
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c212 := h 211 (by decide)
  have h14 : Entails.eval a c993 := derived993 a h
  have h15 : Entails.eval a c927 := derived927 a h
  have h16 : Entails.eval a c33 := h 32 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c991, some c118, some c6, some c113, some c133, some c994, some c53, some c316, some c24, some c4, some c158, some c200, some c22, some c142, some c110, some c987, some c318, some c37, some c261, some c229, some c232, some c209, some c36, some c295, some c927, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p995 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 57) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c991, c118, c6, c113, c133, c994, c53, c316, c24, c4, c158, c200, c22, c142, c110, c987, c318, c37, c261, c229, c232, c209, c36, c295, c927] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c991 := derived991 a h
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c133 := h 132 (by decide)
  have h5 : Entails.eval a c994 := derived994 a h
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c316 := h 315 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c4 := h 3 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c200 := h 199 (by decide)
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  have h15 : Entails.eval a c987 := derived987 a h
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c37 := h 36 (by decide)
  have h18 : Entails.eval a c261 := h 260 (by decide)
  have h19 : Entails.eval a c229 := h 228 (by decide)
  have h20 : Entails.eval a c232 := h 231 (by decide)
  have h21 : Entails.eval a c209 := h 208 (by decide)
  have h22 : Entails.eval a c36 := h 35 (by decide)
  have h23 : Entails.eval a c295 := h 294 (by decide)
  have h24 : Entails.eval a c927 := derived927 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c313, some c6, some c42, some c991, some c53, some c316, some c24, some c4, some c158, some c200, some c22, some c110, some c37, some c263, some c132, some c209, some c36, some c221, some c782, some c271, some c168, some c57, some c64, some c248, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p996 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 57) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c118, c313, c6, c42, c991, c53, c316, c24, c4, c158, c200, c22, c110, c37, c263, c132, c209, c36, c221, c782, c271, c168, c57, c64, c248] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c991 := derived991 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c158 := h 157 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c209 := h 208 (by decide)
  have h17 : Entails.eval a c36 := h 35 (by decide)
  have h18 : Entails.eval a c221 := h 220 (by decide)
  have h19 : Entails.eval a c782 := derived782 a h
  have h20 : Entails.eval a c271 := h 270 (by decide)
  have h21 : Entails.eval a c168 := h 167 (by decide)
  have h22 : Entails.eval a c57 := h 56 (by decide)
  have h23 : Entails.eval a c64 := h 63 (by decide)
  have h24 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c997 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨15, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f997 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c51, some c135, some c112, some c312, some c208, some c238, some c137, some c288, some c81, some c22, some c158, some c224, some c271, some c166, some c57, some c61, some c245, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p997 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked997 : lratChecker f997 p997 = .success := by decide +kernel
theorem unsat997 : Unsatisfiable (PosFin 57) f997 := by
  apply lratCheckerSound f997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p997
  · intro a ha; simp [p997] at ha; subst a; trivial
  · exact checked997
theorem derived997 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c997 := by
  apply localUnsat_implies_entails f997 [c200, c51, c135, c112, c312, c208, c238, c137, c288, c81, c22, c158, c224, c271, c166, c57, c61, c245] c997 unsat997 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c312 := h 311 (by decide)
  have h5 : Entails.eval a c208 := h 207 (by decide)
  have h6 : Entails.eval a c238 := h 237 (by decide)
  have h7 : Entails.eval a c137 := h 136 (by decide)
  have h8 : Entails.eval a c288 := h 287 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c158 := h 157 (by decide)
  have h12 : Entails.eval a c224 := h 223 (by decide)
  have h13 : Entails.eval a c271 := h 270 (by decide)
  have h14 : Entails.eval a c166 := h 165 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c61 := h 60 (by decide)
  have h17 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c998 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨31, by decide⟩, false), (⟨15, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f998 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c312, some c200, some c42, some c51, some c112, some c135, some c997, some c47, some c22, some c32, some c158, some c238, some c224, some c137, some c271, some c166, some c57, some c61, some c245, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p998 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked998 : lratChecker f998 p998 = .success := by decide +kernel
theorem unsat998 : Unsatisfiable (PosFin 57) f998 := by
  apply lratCheckerSound f998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p998
  · intro a ha; simp [p998] at ha; subst a; trivial
  · exact checked998
theorem derived998 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c998 := by
  apply localUnsat_implies_entails f998 [c312, c200, c42, c51, c112, c135, c997, c47, c22, c32, c158, c238, c224, c137, c271, c166, c57, c61, c245] c998 unsat998 (by rfl) a
  have h0 : Entails.eval a c312 := h 311 (by decide)
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c997 := derived997 a h
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c158 := h 157 (by decide)
  have h11 : Entails.eval a c238 := h 237 (by decide)
  have h12 : Entails.eval a c224 := h 223 (by decide)
  have h13 : Entails.eval a c137 := h 136 (by decide)
  have h14 : Entails.eval a c271 := h 270 (by decide)
  have h15 : Entails.eval a c166 := h 165 (by decide)
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c61 := h 60 (by decide)
  have h18 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c999 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨15, by decide⟩, false), (⟨20, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨23, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨10, by decide⟩, false), (⟨18, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c998, some c33, some c36, some c109, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p999 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 57) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c998, c33, c36, c109] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨14, by decide⟩, true), (⟨9, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c6, some c991, some c995, some c42, some c313, some c1, some c996, some c116, some c213, some c200, some c263, some c126, some c10, some c132, some c212, some c999, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1000 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 57) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c118, c6, c991, c995, c42, c313, c1, c996, c116, c213, c200, c263, c126, c10, c132, c212, c999] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c991 := derived991 a h
  have h3 : Entails.eval a c995 := derived995 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c313 := h 312 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c996 := derived996 a h
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c213 := h 212 (by decide)
  have h10 : Entails.eval a c200 := h 199 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c10 := h 9 (by decide)
  have h14 : Entails.eval a c132 := h 131 (by decide)
  have h15 : Entails.eval a c212 := h 211 (by decide)
  have h16 : Entails.eval a c999 := derived999 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, true), (⟨31, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c313, some c42, some c27, some c36, some c271, some c109, some c57, some c65, some c248, some c299, some c298, some c158, some c97, some c186, some c249, some c342, some c160, some c973, some c147, some c339, some c279, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1001 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 57) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c200, c313, c42, c27, c36, c271, c109, c57, c65, c248, c299, c298, c158, c97, c186, c249, c342, c160, c973, c147, c339, c279] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c298 := h 297 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c97 := h 96 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c249 := h 248 (by decide)
  have h16 : Entails.eval a c342 := h 341 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c973 := derived973 a h
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c339 := h 338 (by decide)
  have h21 : Entails.eval a c279 := h 278 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨23, by decide⟩, true), (⟨31, by decide⟩, false), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c271, some c270, some c228, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1002 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 57) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c271, c270, c228] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c271 := h 270 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1003 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨12, by decide⟩, false), (⟨49, by decide⟩, false), (⟨23, by decide⟩, true), (⟨31, by decide⟩, false), (⟨17, by decide⟩, false), (⟨25, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false), (⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1003 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c200, some c298, some c299, some c312, some c313, some c1001, some c51, some c135, some c87, some c233, some c248, some c358, some c365, some c186, some c361, some c89, some c372, some c101, some c295, some c91, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p1003 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1003 : lratChecker f1003 p1003 = .success := by decide +kernel
theorem unsat1003 : Unsatisfiable (PosFin 57) f1003 := by
  apply lratCheckerSound f1003 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1003
  · intro a ha; simp [p1003] at ha; subst a; trivial
  · exact checked1003
theorem derived1003 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1003 := by
  apply localUnsat_implies_entails f1003 [c200, c298, c299, c312, c313, c1001, c51, c135, c87, c233, c248, c358, c365, c186, c361, c89, c372, c101, c295, c91] c1003 unsat1003 (by rfl) a
  have h0 : Entails.eval a c200 := h 199 (by decide)
  have h1 : Entails.eval a c298 := h 297 (by decide)
  have h2 : Entails.eval a c299 := h 298 (by decide)
  have h3 : Entails.eval a c312 := h 311 (by decide)
  have h4 : Entails.eval a c313 := h 312 (by decide)
  have h5 : Entails.eval a c1001 := derived1001 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c233 := h 232 (by decide)
  have h10 : Entails.eval a c248 := h 247 (by decide)
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c365 := h 364 (by decide)
  have h13 : Entails.eval a c186 := h 185 (by decide)
  have h14 : Entails.eval a c361 := h 360 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c372 := h 371 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  have h18 : Entails.eval a c295 := h 294 (by decide)
  have h19 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1004 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨15, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1004 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c197, some c151, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false))]
def p1004 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1004 : lratChecker f1004 p1004 = .success := by decide +kernel
theorem unsat1004 : Unsatisfiable (PosFin 57) f1004 := by
  apply lratCheckerSound f1004 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1004
  · intro a ha; simp [p1004] at ha; subst a; trivial
  · exact checked1004
theorem derived1004 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1004 := by
  apply localUnsat_implies_entails f1004 [c199, c197, c151] c1004 unsat1004 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1005 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨20, by decide⟩, true), (⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1005 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c116, some c53, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1005 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1005 : lratChecker f1005 p1005 = .success := by decide +kernel
theorem unsat1005 : Unsatisfiable (PosFin 57) f1005 := by
  apply lratCheckerSound f1005 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1005
  · intro a ha; simp [p1005] at ha; subst a; trivial
  · exact checked1005
theorem derived1005 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1005 := by
  apply localUnsat_implies_entails f1005 [c11, c116, c53] c1005 unsat1005 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c116 := h 115 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1006 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨13, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1006 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c144, some c9, some c47, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1006 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1006 : lratChecker f1006 p1006 = .success := by decide +kernel
theorem unsat1006 : Unsatisfiable (PosFin 57) f1006 := by
  apply lratCheckerSound f1006 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1006
  · intro a ha; simp [p1006] at ha; subst a; trivial
  · exact checked1006
theorem derived1006 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1006 := by
  apply localUnsat_implies_entails f1006 [c144, c9, c47] c1006 unsat1006 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1007 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1007 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c6, some c204, some c130, some c137, some c229, some c1006, some c200, some c171, some c1005, some c240, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1007 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1007 : lratChecker f1007 p1007 = .success := by decide +kernel
theorem unsat1007 : Unsatisfiable (PosFin 57) f1007 := by
  apply lratCheckerSound f1007 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1007
  · intro a ha; simp [p1007] at ha; subst a; trivial
  · exact checked1007
theorem derived1007 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1007 := by
  apply localUnsat_implies_entails f1007 [c118, c6, c204, c130, c137, c229, c1006, c200, c171, c1005, c240] c1007 unsat1007 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c204 := h 203 (by decide)
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c229 := h 228 (by decide)
  have h6 : Entails.eval a c1006 := derived1006 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c1005 := derived1005 a h
  have h10 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1008 : DefaultClause 57 := directClause [(⟨12, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1008 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c11, some c1005, some c109, some c111, some c267, some c264, some c32, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1008 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1008 : lratChecker f1008 p1008 = .success := by decide +kernel
theorem unsat1008 : Unsatisfiable (PosFin 57) f1008 := by
  apply lratCheckerSound f1008 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1008
  · intro a ha; simp [p1008] at ha; subst a; trivial
  · exact checked1008
theorem derived1008 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1008 := by
  apply localUnsat_implies_entails f1008 [c11, c1005, c109, c111, c267, c264, c32] c1008 unsat1008 (by rfl) a
  have h0 : Entails.eval a c11 := h 10 (by decide)
  have h1 : Entails.eval a c1005 := derived1005 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1009 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨32, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1009 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c267, some c264, some c208, some c215, some c47, some c263, some c32, some c33, some c112, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1009 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1009 : lratChecker f1009 p1009 = .success := by decide +kernel
theorem unsat1009 : Unsatisfiable (PosFin 57) f1009 := by
  apply lratCheckerSound f1009 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1009
  · intro a ha; simp [p1009] at ha; subst a; trivial
  · exact checked1009
theorem derived1009 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1009 := by
  apply localUnsat_implies_entails f1009 [c267, c264, c208, c215, c47, c263, c32, c33, c112] c1009 unsat1009 (by rfl) a
  have h0 : Entails.eval a c267 := h 266 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c208 := h 207 (by decide)
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1010 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨15, by decide⟩, false), (⟨29, by decide⟩, true), (⟨25, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1010 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c313, some c1004, some c6, some c42, some c1, some c1007, some c126, some c10, some c1009, some c1000, some c1008, some c130, some c215, some c776, some c263, some c212, some c1002, some c57, some c1003, some c248, some c9, some c110, some c109, some c101, some c24, some c192, some c550, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1010 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1010 : lratChecker f1010 p1010 = .success := by decide +kernel
theorem unsat1010 : Unsatisfiable (PosFin 57) f1010 := by
  apply lratCheckerSound f1010 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1010
  · intro a ha; simp [p1010] at ha; subst a; trivial
  · exact checked1010
theorem derived1010 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1010 := by
  apply localUnsat_implies_entails f1010 [c118, c313, c1004, c6, c42, c1, c1007, c126, c10, c1009, c1000, c1008, c130, c215, c776, c263, c212, c1002, c57, c1003, c248, c9, c110, c109, c101, c24, c192, c550] c1010 unsat1010 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c1004 := derived1004 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c1007 := derived1007 a h
  have h7 : Entails.eval a c126 := h 125 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c1009 := derived1009 a h
  have h10 : Entails.eval a c1000 := derived1000 a h
  have h11 : Entails.eval a c1008 := derived1008 a h
  have h12 : Entails.eval a c130 := h 129 (by decide)
  have h13 : Entails.eval a c215 := h 214 (by decide)
  have h14 : Entails.eval a c776 := derived776 a h
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c212 := h 211 (by decide)
  have h17 : Entails.eval a c1002 := derived1002 a h
  have h18 : Entails.eval a c57 := h 56 (by decide)
  have h19 : Entails.eval a c1003 := derived1003 a h
  have h20 : Entails.eval a c248 := h 247 (by decide)
  have h21 : Entails.eval a c9 := h 8 (by decide)
  have h22 : Entails.eval a c110 := h 109 (by decide)
  have h23 : Entails.eval a c109 := h 108 (by decide)
  have h24 : Entails.eval a c101 := h 100 (by decide)
  have h25 : Entails.eval a c24 := h 23 (by decide)
  have h26 : Entails.eval a c192 := h 191 (by decide)
  have h27 : Entails.eval a c550 := derived550 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1011 : DefaultClause 57 := directClause [(⟨42, by decide⟩, false), (⟨2, by decide⟩, false), (⟨19, by decide⟩, false), (⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1011 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c233, some c83, some c174, some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1011 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1011 : lratChecker f1011 p1011 = .success := by decide +kernel
theorem unsat1011 : Unsatisfiable (PosFin 57) f1011 := by
  apply lratCheckerSound f1011 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1011
  · intro a ha; simp [p1011] at ha; subst a; trivial
  · exact checked1011
theorem derived1011 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1011 := by
  apply localUnsat_implies_entails f1011 [c233, c83, c174] c1011 unsat1011 (by rfl) a
  have h0 : Entails.eval a c233 := h 232 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c174 := h 173 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1012 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1012 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c118, some c313, some c1010, some c215, some c132, some c263, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1012 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1012 : lratChecker f1012 p1012 = .success := by decide +kernel
theorem unsat1012 : Unsatisfiable (PosFin 57) f1012 := by
  apply lratCheckerSound f1012 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1012
  · intro a ha; simp [p1012] at ha; subst a; trivial
  · exact checked1012
theorem derived1012 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1012 := by
  apply localUnsat_implies_entails f1012 [c118, c313, c1010, c215, c132, c263] c1012 unsat1012 (by rfl) a
  have h0 : Entails.eval a c118 := h 117 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c1010 := derived1010 a h
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1013 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨21, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨29, by decide⟩, true), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1013 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c215, some c55, some c37, some c39, some c111, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1013 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1013 : lratChecker f1013 p1013 = .success := by decide +kernel
theorem unsat1013 : Unsatisfiable (PosFin 57) f1013 := by
  apply lratCheckerSound f1013 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1013
  · intro a ha; simp [p1013] at ha; subst a; trivial
  · exact checked1013
theorem derived1013 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1013 := by
  apply localUnsat_implies_entails f1013 [c215, c55, c37, c39, c111] c1013 unsat1013 (by rfl) a
  have h0 : Entails.eval a c215 := h 214 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1013

end CochromaticTwenty.Certificates.B16_0_2Enumerating
