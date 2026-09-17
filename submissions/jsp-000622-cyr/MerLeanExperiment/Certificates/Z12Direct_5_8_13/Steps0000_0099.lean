import MerLeanExperiment.Certificates.Z12Direct_5_8_13.Inputs

/-! Generated from the actual pinned z12direct_5_8_13-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_13
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c903 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨23, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f903 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c82, some c84, some c203, some c25, some c21, some c224, some c322, some c272, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p903 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked903 : lratChecker f903 p903 = .success := by decide +kernel
theorem unsat903 : Unsatisfiable (PosFin 31) f903 := by
  apply lratCheckerSound f903 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p903
  · intro a ha; simp [p903] at ha; subst a; trivial
  · exact checked903
theorem derived903 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c903 := by
  apply localUnsat_implies_entails f903 [c82, c84, c203, c25, c21, c224, c322, c272] c903 unsat903 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c203 := h 202 (by decide)
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c224 := h 223 (by decide)
  have h6 : Entails.eval a c322 := h 321 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c904 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f904 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c82, some c81, some c48, some c138, some c83, some c202, some c25, some c842, some c203, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p904 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked904 : lratChecker f904 p904 = .success := by decide +kernel
theorem unsat904 : Unsatisfiable (PosFin 31) f904 := by
  apply lratCheckerSound f904 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p904
  · intro a ha; simp [p904] at ha; subst a; trivial
  · exact checked904
theorem derived904 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c904 := by
  apply localUnsat_implies_entails f904 [c82, c81, c48, c138, c83, c202, c25, c842, c203] c904 unsat904 (by rfl) a
  have h0 : Entails.eval a c82 := h 81 (by decide)
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c842 := h 841 (by decide)
  have h8 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c905 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f905 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c82, some c904, some c139, some c84, some c203, some c25, some c202, some c83, some c847, some c138, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p905 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked905 : lratChecker f905 p905 = .success := by decide +kernel
theorem unsat905 : Unsatisfiable (PosFin 31) f905 := by
  apply lratCheckerSound f905 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p905
  · intro a ha; simp [p905] at ha; subst a; trivial
  · exact checked905
theorem derived905 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c905 := by
  apply localUnsat_implies_entails f905 [c81, c82, c904, c139, c84, c203, c25, c202, c83, c847, c138] c905 unsat905 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c82 := h 81 (by decide)
  have h2 : Entails.eval a c904 := derived904 a h
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c203 := h 202 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c847 := h 846 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c906 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f906 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c905, some c81, some c48, some c49, some c55, some c170, some c264, some c310, some c454, some c494, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p906 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked906 : lratChecker f906 p906 = .success := by decide +kernel
theorem unsat906 : Unsatisfiable (PosFin 31) f906 := by
  apply lratCheckerSound f906 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p906
  · intro a ha; simp [p906] at ha; subst a; trivial
  · exact checked906
theorem derived906 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c906 := by
  apply localUnsat_implies_entails f906 [c905, c81, c48, c49, c55, c170, c264, c310, c454, c494] c906 unsat906 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c310 := h 309 (by decide)
  have h8 : Entails.eval a c454 := h 453 (by decide)
  have h9 : Entails.eval a c494 := h 493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c907 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f907 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c905, some c81, some c906, some c138, some c83, some c202, some c25, some c26, some c32, some c229, some c327, some c183, some c276, some c579, some c591, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p907 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked907 : lratChecker f907 p907 = .success := by decide +kernel
theorem unsat907 : Unsatisfiable (PosFin 31) f907 := by
  apply lratCheckerSound f907 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p907
  · intro a ha; simp [p907] at ha; subst a; trivial
  · exact checked907
theorem derived907 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c907 := by
  apply localUnsat_implies_entails f907 [c905, c81, c906, c138, c83, c202, c25, c26, c32, c229, c327, c183, c276, c579, c591] c907 unsat907 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c906 := derived906 a h
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c229 := h 228 (by decide)
  have h10 : Entails.eval a c327 := h 326 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c579 := h 578 (by decide)
  have h14 : Entails.eval a c591 := h 590 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c908 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f908 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c905, some c81, some c83, some c202, some c25, some c26, some c32, some c229, some c327, some c276, some c454, some c686, some c676, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p908 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked908 : lratChecker f908 p908 = .success := by decide +kernel
theorem unsat908 : Unsatisfiable (PosFin 31) f908 := by
  apply lratCheckerSound f908 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p908
  · intro a ha; simp [p908] at ha; subst a; trivial
  · exact checked908
theorem derived908 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c908 := by
  apply localUnsat_implies_entails f908 [c905, c81, c83, c202, c25, c26, c32, c229, c327, c276, c454, c686, c676] c908 unsat908 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c32 := h 31 (by decide)
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c327 := h 326 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c454 := h 453 (by decide)
  have h11 : Entails.eval a c686 := h 685 (by decide)
  have h12 : Entails.eval a c676 := h 675 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c909 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f909 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c905, some c81, some c907, some c908, some c138, some c48, some c49, some c42, some c55, some c170, some c264, some c285, some c310, some c387, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p909 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked909 : lratChecker f909 p909 = .success := by decide +kernel
theorem unsat909 : Unsatisfiable (PosFin 31) f909 := by
  apply lratCheckerSound f909 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p909
  · intro a ha; simp [p909] at ha; subst a; trivial
  · exact checked909
theorem derived909 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c909 := by
  apply localUnsat_implies_entails f909 [c905, c81, c907, c908, c138, c48, c49, c42, c55, c170, c264, c285, c310, c387] c909 unsat909 (by rfl) a
  have h0 : Entails.eval a c905 := derived905 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c907 := derived907 a h
  have h3 : Entails.eval a c908 := derived908 a h
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c310 := h 309 (by decide)
  have h13 : Entails.eval a c387 := h 386 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c910 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f910 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c909, some c905, some c81, some c49, some c140, some c85, some c204, some c26, some c772, some c202, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p910 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked910 : lratChecker f910 p910 = .success := by decide +kernel
theorem unsat910 : Unsatisfiable (PosFin 31) f910 := by
  apply lratCheckerSound f910 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p910
  · intro a ha; simp [p910] at ha; subst a; trivial
  · exact checked910
theorem derived910 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c910 := by
  apply localUnsat_implies_entails f910 [c909, c905, c81, c49, c140, c85, c204, c26, c772, c202] c910 unsat910 (by rfl) a
  have h0 : Entails.eval a c909 := derived909 a h
  have h1 : Entails.eval a c905 := derived905 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c772 := h 771 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c911 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f911 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c905, some c909, some c910, some c138, some c83, some c202, some c26, some c204, some c761, some c85, some c140, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p911 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked911 : lratChecker f911 p911 = .success := by decide +kernel
theorem unsat911 : Unsatisfiable (PosFin 31) f911 := by
  apply lratCheckerSound f911 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p911
  · intro a ha; simp [p911] at ha; subst a; trivial
  · exact checked911
theorem derived911 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c911 := by
  apply localUnsat_implies_entails f911 [c81, c905, c909, c910, c138, c83, c202, c26, c204, c761, c85, c140] c911 unsat911 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c905 := derived905 a h
  have h2 : Entails.eval a c909 := derived909 a h
  have h3 : Entails.eval a c910 := derived910 a h
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c761 := h 760 (by decide)
  have h10 : Entails.eval a c85 := h 84 (by decide)
  have h11 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c912 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨21, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f912 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c202, some c102, some c230, some c19, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p912 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked912 : lratChecker f912 p912 = .success := by decide +kernel
theorem unsat912 : Unsatisfiable (PosFin 31) f912 := by
  apply lratCheckerSound f912 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p912
  · intro a ha; simp [p912] at ha; subst a; trivial
  · exact checked912
theorem derived912 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c912 := by
  apply localUnsat_implies_entails f912 [c83, c202, c102, c230, c19] c912 unsat912 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c102 := h 101 (by decide)
  have h3 : Entails.eval a c230 := h 229 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c913 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f913 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c202, some c81, some c912, some c358, some c603, some c80, some c748, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p913 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked913 : lratChecker f913 p913 = .success := by decide +kernel
theorem unsat913 : Unsatisfiable (PosFin 31) f913 := by
  apply lratCheckerSound f913 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p913
  · intro a ha; simp [p913] at ha; subst a; trivial
  · exact checked913
theorem derived913 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c913 := by
  apply localUnsat_implies_entails f913 [c83, c202, c81, c912, c358, c603, c80, c748] c913 unsat913 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c912 := derived912 a h
  have h4 : Entails.eval a c358 := h 357 (by decide)
  have h5 : Entails.eval a c603 := h 602 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c748 := h 747 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c914 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f914 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c202, some c183, some c19, some c230, some c327, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p914 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked914 : lratChecker f914 p914 = .success := by decide +kernel
theorem unsat914 : Unsatisfiable (PosFin 31) f914 := by
  apply lratCheckerSound f914 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p914
  · intro a ha; simp [p914] at ha; subst a; trivial
  · exact checked914
theorem derived914 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c914 := by
  apply localUnsat_implies_entails f914 [c83, c202, c183, c19, c230, c327] c914 unsat914 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c183 := h 182 (by decide)
  have h3 : Entails.eval a c19 := h 18 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c327 := h 326 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c915 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f915 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c83, some c202, some c911, some c81, some c913, some c914, some c76, some c182, some c828, some c602, some c677, some c117, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p915 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked915 : lratChecker f915 p915 = .success := by decide +kernel
theorem unsat915 : Unsatisfiable (PosFin 31) f915 := by
  apply lratCheckerSound f915 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p915
  · intro a ha; simp [p915] at ha; subst a; trivial
  · exact checked915
theorem derived915 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c915 := by
  apply localUnsat_implies_entails f915 [c83, c202, c911, c81, c913, c914, c76, c182, c828, c602, c677, c117] c915 unsat915 (by rfl) a
  have h0 : Entails.eval a c83 := h 82 (by decide)
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c913 := derived913 a h
  have h5 : Entails.eval a c914 := derived914 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c182 := h 181 (by decide)
  have h8 : Entails.eval a c828 := h 827 (by decide)
  have h9 : Entails.eval a c602 := h 601 (by decide)
  have h10 : Entails.eval a c677 := h 676 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c916 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨15, by decide⟩, false), (⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f916 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c121, some c122, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p916 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked916 : lratChecker f916 p916 = .success := by decide +kernel
theorem unsat916 : Unsatisfiable (PosFin 31) f916 := by
  apply lratCheckerSound f916 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p916
  · intro a ha; simp [p916] at ha; subst a; trivial
  · exact checked916
theorem derived916 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c916 := by
  apply localUnsat_implies_entails f916 [c121, c122] c916 unsat916 (by rfl) a
  have h0 : Entails.eval a c121 := h 120 (by decide)
  have h1 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c917 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f917 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c83, some c202, some c26, some c915, some c761, some c916, some c579, some c66, some c69, some c845, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p917 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked917 : lratChecker f917 p917 = .success := by decide +kernel
theorem unsat917 : Unsatisfiable (PosFin 31) f917 := by
  apply lratCheckerSound f917 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p917
  · intro a ha; simp [p917] at ha; subst a; trivial
  · exact checked917
theorem derived917 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c917 := by
  apply localUnsat_implies_entails f917 [c81, c83, c202, c26, c915, c761, c916, c579, c66, c69, c845] c917 unsat917 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c915 := derived915 a h
  have h5 : Entails.eval a c761 := h 760 (by decide)
  have h6 : Entails.eval a c916 := derived916 a h
  have h7 : Entails.eval a c579 := h 578 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c845 := h 844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c918 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨3, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f918 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c138, some c49, some c358, some c257, some c559, some c134, some c362, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p918 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked918 : lratChecker f918 p918 = .success := by decide +kernel
theorem unsat918 : Unsatisfiable (PosFin 31) f918 := by
  apply lratCheckerSound f918 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p918
  · intro a ha; simp [p918] at ha; subst a; trivial
  · exact checked918
theorem derived918 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c918 := by
  apply localUnsat_implies_entails f918 [c81, c138, c49, c358, c257, c559, c134, c362] c918 unsat918 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c559 := h 558 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c362 := h 361 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c919 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨14, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f919 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c901, some c869, some c742, some c702, some c7, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p919 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked919 : lratChecker f919 p919 = .success := by decide +kernel
theorem unsat919 : Unsatisfiable (PosFin 31) f919 := by
  apply lratCheckerSound f919 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p919
  · intro a ha; simp [p919] at ha; subst a; trivial
  · exact checked919
theorem derived919 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c919 := by
  apply localUnsat_implies_entails f919 [c901, c869, c742, c702, c7] c919 unsat919 (by rfl) a
  have h0 : Entails.eval a c901 := h 900 (by decide)
  have h1 : Entails.eval a c869 := h 868 (by decide)
  have h2 : Entails.eval a c742 := h 741 (by decide)
  have h3 : Entails.eval a c702 := h 701 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c920 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨10, by decide⟩, true), (⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨7, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f920 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c438, some c817, some c540, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p920 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked920 : lratChecker f920 p920 = .success := by decide +kernel
theorem unsat920 : Unsatisfiable (PosFin 31) f920 := by
  apply lratCheckerSound f920 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p920
  · intro a ha; simp [p920] at ha; subst a; trivial
  · exact checked920
theorem derived920 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c920 := by
  apply localUnsat_implies_entails f920 [c438, c817, c540] c920 unsat920 (by rfl) a
  have h0 : Entails.eval a c438 := h 437 (by decide)
  have h1 : Entails.eval a c817 := h 816 (by decide)
  have h2 : Entails.eval a c540 := h 539 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c921 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f921 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c917, some c138, some c49, some c26, some c918, some c303, some c919, some c76, some c257, some c361, some c120, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p921 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked921 : lratChecker f921 p921 = .success := by decide +kernel
theorem unsat921 : Unsatisfiable (PosFin 31) f921 := by
  apply lratCheckerSound f921 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p921
  · intro a ha; simp [p921] at ha; subst a; trivial
  · exact checked921
theorem derived921 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c921 := by
  apply localUnsat_implies_entails f921 [c81, c917, c138, c49, c26, c918, c303, c919, c76, c257, c361, c120] c921 unsat921 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c917 := derived917 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c918 := derived918 a h
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c919 := derived919 a h
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c361 := h 360 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c922 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f922 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c921, some c202, some c81, some c917, some c138, some c49, some c918, some c303, some c33, some c242, some c171, some c264, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p922 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked922 : lratChecker f922 p922 = .success := by decide +kernel
theorem unsat922 : Unsatisfiable (PosFin 31) f922 := by
  apply lratCheckerSound f922 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p922
  · intro a ha; simp [p922] at ha; subst a; trivial
  · exact checked922
theorem derived922 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c922 := by
  apply localUnsat_implies_entails f922 [c921, c202, c81, c917, c138, c49, c918, c303, c33, c242, c171, c264] c922 unsat922 (by rfl) a
  have h0 : Entails.eval a c921 := derived921 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c917 := derived917 a h
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c918 := derived918 a h
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c242 := h 241 (by decide)
  have h10 : Entails.eval a c171 := h 170 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c923 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f923 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c917, some c138, some c921, some c202, some c922, some c772, some c81, some c49, some c210, some c377, some c33, some c95, some c264, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p923 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked923 : lratChecker f923 p923 = .success := by decide +kernel
theorem unsat923 : Unsatisfiable (PosFin 31) f923 := by
  apply lratCheckerSound f923 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p923
  · intro a ha; simp [p923] at ha; subst a; trivial
  · exact checked923
theorem derived923 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c923 := by
  apply localUnsat_implies_entails f923 [c917, c138, c921, c202, c922, c772, c81, c49, c210, c377, c33, c95, c264] c923 unsat923 (by rfl) a
  have h0 : Entails.eval a c917 := derived917 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c921 := derived921 a h
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c922 := derived922 a h
  have h5 : Entails.eval a c772 := h 771 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c377 := h 376 (by decide)
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c924 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true), (⟨9, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f924 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c95, some c55, some c42, some c454, some c494, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p924 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked924 : lratChecker f924 p924 = .success := by decide +kernel
theorem unsat924 : Unsatisfiable (PosFin 31) f924 := by
  apply lratCheckerSound f924 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p924
  · intro a ha; simp [p924] at ha; subst a; trivial
  · exact checked924
theorem derived924 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c924 := by
  apply localUnsat_implies_entails f924 [c33, c95, c55, c42, c454, c494] c924 unsat924 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c454 := h 453 (by decide)
  have h5 : Entails.eval a c494 := h 493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c925 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f925 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c917, some c138, some c49, some c921, some c202, some c922, some c772, some c923, some c924, some c90, some c814, some c636, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p925 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked925 : lratChecker f925 p925 = .success := by decide +kernel
theorem unsat925 : Unsatisfiable (PosFin 31) f925 := by
  apply lratCheckerSound f925 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p925
  · intro a ha; simp [p925] at ha; subst a; trivial
  · exact checked925
theorem derived925 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c925 := by
  apply localUnsat_implies_entails f925 [c81, c917, c138, c49, c921, c202, c922, c772, c923, c924, c90, c814, c636] c925 unsat925 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c917 := derived917 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c921 := derived921 a h
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c922 := derived922 a h
  have h7 : Entails.eval a c772 := h 771 (by decide)
  have h8 : Entails.eval a c923 := derived923 a h
  have h9 : Entails.eval a c924 := derived924 a h
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c814 := h 813 (by decide)
  have h12 : Entails.eval a c636 := h 635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c926 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f926 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c925, some c81, some c26, some c202, some c83, some c138, some c48, some c55, some c171, some c264, some c608, some c310, some c609, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p926 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked926 : lratChecker f926 p926 = .success := by decide +kernel
theorem unsat926 : Unsatisfiable (PosFin 31) f926 := by
  apply lratCheckerSound f926 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p926
  · intro a ha; simp [p926] at ha; subst a; trivial
  · exact checked926
theorem derived926 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c926 := by
  apply localUnsat_implies_entails f926 [c925, c81, c26, c202, c83, c138, c48, c55, c171, c264, c608, c310, c609] c926 unsat926 (by rfl) a
  have h0 : Entails.eval a c925 := derived925 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c608 := h 607 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  have h12 : Entails.eval a c609 := h 608 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c927 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f927 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c926, some c925, some c81, some c4, some c25, some c202, some c83, some c918, some c171, some c310, some c264, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p927 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked927 : lratChecker f927 p927 = .success := by decide +kernel
theorem unsat927 : Unsatisfiable (PosFin 31) f927 := by
  apply lratCheckerSound f927 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p927
  · intro a ha; simp [p927] at ha; subst a; trivial
  · exact checked927
theorem derived927 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c927 := by
  apply localUnsat_implies_entails f927 [c926, c925, c81, c4, c25, c202, c83, c918, c171, c310, c264] c927 unsat927 (by rfl) a
  have h0 : Entails.eval a c926 := derived926 a h
  have h1 : Entails.eval a c925 := derived925 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c4 := h 3 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c918 := derived918 a h
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c310 := h 309 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c928 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f928 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c925, some c81, some c926, some c927, some c48, some c138, some c83, some c914, some c202, some c257, some c25, some c358, some c230, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p928 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked928 : lratChecker f928 p928 = .success := by decide +kernel
theorem unsat928 : Unsatisfiable (PosFin 31) f928 := by
  apply lratCheckerSound f928 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p928
  · intro a ha; simp [p928] at ha; subst a; trivial
  · exact checked928
theorem derived928 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c928 := by
  apply localUnsat_implies_entails f928 [c925, c81, c926, c927, c48, c138, c83, c914, c202, c257, c25, c358, c230] c928 unsat928 (by rfl) a
  have h0 : Entails.eval a c925 := derived925 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c926 := derived926 a h
  have h3 : Entails.eval a c927 := derived927 a h
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c914 := derived914 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c25 := h 24 (by decide)
  have h11 : Entails.eval a c358 := h 357 (by decide)
  have h12 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c929 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f929 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c925, some c928, some c49, some c138, some c83, some c202, some c25, some c26, some c32, some c230, some c579, some c327, some c591, some c276, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p929 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked929 : lratChecker f929 p929 = .success := by decide +kernel
theorem unsat929 : Unsatisfiable (PosFin 31) f929 := by
  apply lratCheckerSound f929 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p929
  · intro a ha; simp [p929] at ha; subst a; trivial
  · exact checked929
theorem derived929 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c929 := by
  apply localUnsat_implies_entails f929 [c81, c925, c928, c49, c138, c83, c202, c25, c26, c32, c230, c579, c327, c591, c276] c929 unsat929 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c925 := derived925 a h
  have h2 : Entails.eval a c928 := derived928 a h
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c579 := h 578 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c591 := h 590 (by decide)
  have h14 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c930 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f930 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c138, some c83, some c202, some c929, some c81, some c32, some c230, some c327, some c276, some c395, some c606, some c593, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p930 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked930 : lratChecker f930 p930 = .success := by decide +kernel
theorem unsat930 : Unsatisfiable (PosFin 31) f930 := by
  apply lratCheckerSound f930 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p930
  · intro a ha; simp [p930] at ha; subst a; trivial
  · exact checked930
theorem derived930 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c930 := by
  apply localUnsat_implies_entails f930 [c138, c83, c202, c929, c81, c32, c230, c327, c276, c395, c606, c593] c930 unsat930 (by rfl) a
  have h0 : Entails.eval a c138 := h 137 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c202 := h 201 (by decide)
  have h3 : Entails.eval a c929 := derived929 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c230 := h 229 (by decide)
  have h7 : Entails.eval a c327 := h 326 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  have h9 : Entails.eval a c395 := h 394 (by decide)
  have h10 : Entails.eval a c606 := h 605 (by decide)
  have h11 : Entails.eval a c593 := h 592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c931 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f931 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c81, some c138, some c83, some c202, some c930, some c25, some c19, some c761, some c74, some c68, some c916, some c130, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p931 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked931 : lratChecker f931 p931 = .success := by decide +kernel
theorem unsat931 : Unsatisfiable (PosFin 31) f931 := by
  apply lratCheckerSound f931 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p931
  · intro a ha; simp [p931] at ha; subst a; trivial
  · exact checked931
theorem derived931 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c931 := by
  apply localUnsat_implies_entails f931 [c929, c81, c138, c83, c202, c930, c25, c19, c761, c74, c68, c916, c130] c931 unsat931 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c930 := derived930 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c761 := h 760 (by decide)
  have h9 : Entails.eval a c74 := h 73 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c916 := derived916 a h
  have h12 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c932 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f932 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c931, some c929, some c86, some c141, some c156, some c327, some c494, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p932 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked932 : lratChecker f932 p932 = .success := by decide +kernel
theorem unsat932 : Unsatisfiable (PosFin 31) f932 := by
  apply lratCheckerSound f932 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p932
  · intro a ha; simp [p932] at ha; subst a; trivial
  · exact checked932
theorem derived932 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c932 := by
  apply localUnsat_implies_entails f932 [c931, c929, c86, c141, c156, c327, c494] c932 unsat932 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c929 := derived929 a h
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c327 := h 326 (by decide)
  have h6 : Entails.eval a c494 := h 493 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c933 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f933 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c81, some c847, some c771, some c202, some c768, some c214, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p933 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked933 : lratChecker f933 p933 = .success := by decide +kernel
theorem unsat933 : Unsatisfiable (PosFin 31) f933 := by
  apply lratCheckerSound f933 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p933
  · intro a ha; simp [p933] at ha; subst a; trivial
  · exact checked933
theorem derived933 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c933 := by
  apply localUnsat_implies_entails f933 [c929, c81, c847, c771, c202, c768, c214] c933 unsat933 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c847 := h 846 (by decide)
  have h3 : Entails.eval a c771 := h 770 (by decide)
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c768 := h 767 (by decide)
  have h6 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c934 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f934 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c205, some c156, some c121, some c395, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p934 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked934 : lratChecker f934 p934 = .success := by decide +kernel
theorem unsat934 : Unsatisfiable (PosFin 31) f934 := by
  apply lratCheckerSound f934 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p934
  · intro a ha; simp [p934] at ha; subst a; trivial
  · exact checked934
theorem derived934 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c934 := by
  apply localUnsat_implies_entails f934 [c929, c205, c156, c121, c395] c934 unsat934 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c395 := h 394 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c935 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f935 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c931, some c929, some c911, some c932, some c205, some c934, some c933, some c230, some c895, some c711, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p935 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked935 : lratChecker f935 p935 = .success := by decide +kernel
theorem unsat935 : Unsatisfiable (PosFin 31) f935 := by
  apply lratCheckerSound f935 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p935
  · intro a ha; simp [p935] at ha; subst a; trivial
  · exact checked935
theorem derived935 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c935 := by
  apply localUnsat_implies_entails f935 [c931, c929, c911, c932, c205, c934, c933, c230, c895, c711] c935 unsat935 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c929 := derived929 a h
  have h2 : Entails.eval a c911 := derived911 a h
  have h3 : Entails.eval a c932 := derived932 a h
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c934 := derived934 a h
  have h6 : Entails.eval a c933 := derived933 a h
  have h7 : Entails.eval a c230 := h 229 (by decide)
  have h8 : Entails.eval a c895 := h 894 (by decide)
  have h9 : Entails.eval a c711 := h 710 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c936 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f936 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c931, some c81, some c935, some c48, some c230, some c302, some c34, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p936 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked936 : lratChecker f936 p936 = .success := by decide +kernel
theorem unsat936 : Unsatisfiable (PosFin 31) f936 := by
  apply lratCheckerSound f936 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p936
  · intro a ha; simp [p936] at ha; subst a; trivial
  · exact checked936
theorem derived936 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c936 := by
  apply localUnsat_implies_entails f936 [c931, c81, c935, c48, c230, c302, c34] c936 unsat936 (by rfl) a
  have h0 : Entails.eval a c931 := derived931 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c935 := derived935 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c302 := h 301 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c937 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f937 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c935, some c931, some c81, some c936, some c25, some c209, some c202, some c34, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p937 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked937 : lratChecker f937 p937 = .success := by decide +kernel
theorem unsat937 : Unsatisfiable (PosFin 31) f937 := by
  apply lratCheckerSound f937 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p937
  · intro a ha; simp [p937] at ha; subst a; trivial
  · exact checked937
theorem derived937 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c937 := by
  apply localUnsat_implies_entails f937 [c935, c931, c81, c936, c25, c209, c202, c34] c937 unsat937 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c936 := derived936 a h
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c209 := h 208 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c938 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f938 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c935, some c931, some c929, some c81, some c25, some c202, some c847, some c34, some c156, some c572, some c755, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p938 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked938 : lratChecker f938 p938 = .success := by decide +kernel
theorem unsat938 : Unsatisfiable (PosFin 31) f938 := by
  apply lratCheckerSound f938 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p938
  · intro a ha; simp [p938] at ha; subst a; trivial
  · exact checked938
theorem derived938 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c938 := by
  apply localUnsat_implies_entails f938 [c935, c931, c929, c81, c25, c202, c847, c34, c156, c572, c755] c938 unsat938 (by rfl) a
  have h0 : Entails.eval a c935 := derived935 a h
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c847 := h 846 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c156 := h 155 (by decide)
  have h9 : Entails.eval a c572 := h 571 (by decide)
  have h10 : Entails.eval a c755 := h 754 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c939 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f939 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c931, some c935, some c48, some c937, some c938, some c327, some c454, some c276, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p939 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked939 : lratChecker f939 p939 = .success := by decide +kernel
theorem unsat939 : Unsatisfiable (PosFin 31) f939 := by
  apply lratCheckerSound f939 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p939
  · intro a ha; simp [p939] at ha; subst a; trivial
  · exact checked939
theorem derived939 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c939 := by
  apply localUnsat_implies_entails f939 [c81, c931, c935, c48, c937, c938, c327, c454, c276] c939 unsat939 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c931 := derived931 a h
  have h2 : Entails.eval a c935 := derived935 a h
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c937 := derived937 a h
  have h5 : Entails.eval a c938 := derived938 a h
  have h6 : Entails.eval a c327 := h 326 (by decide)
  have h7 : Entails.eval a c454 := h 453 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c940 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f940 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c939, some c81, some c263, some c387, some c302, some c820, some c328, some c640, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p940 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked940 : lratChecker f940 p940 = .success := by decide +kernel
theorem unsat940 : Unsatisfiable (PosFin 31) f940 := by
  apply lratCheckerSound f940 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p940
  · intro a ha; simp [p940] at ha; subst a; trivial
  · exact checked940
theorem derived940 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c940 := by
  apply localUnsat_implies_entails f940 [c939, c81, c263, c387, c302, c820, c328, c640] c940 unsat940 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c387 := h 386 (by decide)
  have h4 : Entails.eval a c302 := h 301 (by decide)
  have h5 : Entails.eval a c820 := h 819 (by decide)
  have h6 : Entails.eval a c328 := h 327 (by decide)
  have h7 : Entails.eval a c640 := h 639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c941 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f941 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c911, some c81, some c940, some c78, some c172, some c256, some c147, some c454, some c283, some c666, some c295, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p941 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked941 : lratChecker f941 p941 = .success := by decide +kernel
theorem unsat941 : Unsatisfiable (PosFin 31) f941 := by
  apply lratCheckerSound f941 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p941
  · intro a ha; simp [p941] at ha; subst a; trivial
  · exact checked941
theorem derived941 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c941 := by
  apply localUnsat_implies_entails f941 [c929, c911, c81, c940, c78, c172, c256, c147, c454, c283, c666, c295] c941 unsat941 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c911 := derived911 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c940 := derived940 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c172 := h 171 (by decide)
  have h6 : Entails.eval a c256 := h 255 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c454 := h 453 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c666 := h 665 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c942 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f942 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c48, some c929, some c158, some c154, some c144, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p942 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked942 : lratChecker f942 p942 = .success := by decide +kernel
theorem unsat942 : Unsatisfiable (PosFin 31) f942 := by
  apply lratCheckerSound f942 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p942
  · intro a ha; simp [p942] at ha; subst a; trivial
  · exact checked942
theorem derived942 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c942 := by
  apply localUnsat_implies_entails f942 [c81, c48, c929, c158, c154, c144] c942 unsat942 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c943 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f943 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c939, some c929, some c81, some c48, some c942, some c141, some c150, some c387, some c772, some c857, some c202, some c855, some c219, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p943 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked943 : lratChecker f943 p943 = .success := by decide +kernel
theorem unsat943 : Unsatisfiable (PosFin 31) f943 := by
  apply lratCheckerSound f943 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p943
  · intro a ha; simp [p943] at ha; subst a; trivial
  · exact checked943
theorem derived943 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c943 := by
  apply localUnsat_implies_entails f943 [c939, c929, c81, c48, c942, c141, c150, c387, c772, c857, c202, c855, c219] c943 unsat943 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c929 := derived929 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c48 := h 47 (by decide)
  have h4 : Entails.eval a c942 := derived942 a h
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c150 := h 149 (by decide)
  have h7 : Entails.eval a c387 := h 386 (by decide)
  have h8 : Entails.eval a c772 := h 771 (by decide)
  have h9 : Entails.eval a c857 := h 856 (by decide)
  have h10 : Entails.eval a c202 := h 201 (by decide)
  have h11 : Entails.eval a c855 := h 854 (by decide)
  have h12 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c944 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f944 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c943, some c941, some c929, some c141, some c156, some c494, some c933, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p944 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked944 : lratChecker f944 p944 = .success := by decide +kernel
theorem unsat944 : Unsatisfiable (PosFin 31) f944 := by
  apply lratCheckerSound f944 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p944
  · intro a ha; simp [p944] at ha; subst a; trivial
  · exact checked944
theorem derived944 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c944 := by
  apply localUnsat_implies_entails f944 [c943, c941, c929, c141, c156, c494, c933] c944 unsat944 (by rfl) a
  have h0 : Entails.eval a c943 := derived943 a h
  have h1 : Entails.eval a c941 := derived941 a h
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c494 := h 493 (by decide)
  have h6 : Entails.eval a c933 := derived933 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c945 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f945 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c943, some c941, some c929, some c944, some c86, some c934, some c933, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p945 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked945 : lratChecker f945 p945 = .success := by decide +kernel
theorem unsat945 : Unsatisfiable (PosFin 31) f945 := by
  apply lratCheckerSound f945 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p945
  · intro a ha; simp [p945] at ha; subst a; trivial
  · exact checked945
theorem derived945 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c945 := by
  apply localUnsat_implies_entails f945 [c943, c941, c929, c944, c86, c934, c933] c945 unsat945 (by rfl) a
  have h0 : Entails.eval a c943 := derived943 a h
  have h1 : Entails.eval a c941 := derived941 a h
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c944 := derived944 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c934 := derived934 a h
  have h6 : Entails.eval a c933 := derived933 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c946 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f946 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c939, some c929, some c81, some c943, some c941, some c945, some c25, some c202, some c847, some c34, some c156, some c209, some c813, some c636, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p946 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked946 : lratChecker f946 p946 = .success := by decide +kernel
theorem unsat946 : Unsatisfiable (PosFin 31) f946 := by
  apply lratCheckerSound f946 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p946
  · intro a ha; simp [p946] at ha; subst a; trivial
  · exact checked946
theorem derived946 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c946 := by
  apply localUnsat_implies_entails f946 [c939, c929, c81, c943, c941, c945, c25, c202, c847, c34, c156, c209, c813, c636] c946 unsat946 (by rfl) a
  have h0 : Entails.eval a c939 := derived939 a h
  have h1 : Entails.eval a c929 := derived929 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c943 := derived943 a h
  have h4 : Entails.eval a c941 := derived941 a h
  have h5 : Entails.eval a c945 := derived945 a h
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c847 := h 846 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c209 := h 208 (by decide)
  have h12 : Entails.eval a c813 := h 812 (by decide)
  have h13 : Entails.eval a c636 := h 635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c947 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨21, by decide⟩, false), (⟨1, by decide⟩, true), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f947 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c19, some c25, some c74, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p947 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked947 : lratChecker f947 p947 = .success := by decide +kernel
theorem unsat947 : Unsatisfiable (PosFin 31) f947 := by
  apply lratCheckerSound f947 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p947
  · intro a ha; simp [p947] at ha; subst a; trivial
  · exact checked947
theorem derived947 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c947 := by
  apply localUnsat_implies_entails f947 [c19, c25, c74] c947 unsat947 (by rfl) a
  have h0 : Entails.eval a c19 := h 18 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c948 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f948 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c946, some c138, some c83, some c202, some c939, some c929, some c761, some c68, some c916, some c220, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p948 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked948 : lratChecker f948 p948 = .success := by decide +kernel
theorem unsat948 : Unsatisfiable (PosFin 31) f948 := by
  apply lratCheckerSound f948 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p948
  · intro a ha; simp [p948] at ha; subst a; trivial
  · exact checked948
theorem derived948 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c948 := by
  apply localUnsat_implies_entails f948 [c946, c138, c83, c202, c939, c929, c761, c68, c916, c220] c948 unsat948 (by rfl) a
  have h0 : Entails.eval a c946 := derived946 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c939 := derived939 a h
  have h5 : Entails.eval a c929 := derived929 a h
  have h6 : Entails.eval a c761 := h 760 (by decide)
  have h7 : Entails.eval a c68 := h 67 (by decide)
  have h8 : Entails.eval a c916 := derived916 a h
  have h9 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c949 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨21, by decide⟩, false), (⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f949 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c70, some c107, some c826, some c811, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p949 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked949 : lratChecker f949 p949 = .success := by decide +kernel
theorem unsat949 : Unsatisfiable (PosFin 31) f949 := by
  apply lratCheckerSound f949 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p949
  · intro a ha; simp [p949] at ha; subst a; trivial
  · exact checked949
theorem derived949 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c949 := by
  apply localUnsat_implies_entails f949 [c70, c107, c826, c811] c949 unsat949 (by rfl) a
  have h0 : Entails.eval a c70 := h 69 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c826 := h 825 (by decide)
  have h3 : Entails.eval a c811 := h 810 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c950 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f950 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c911, some c81, some c939, some c946, some c138, some c83, some c202, some c20, some c78, some c947, some c948, some c949, some c891, some c700, some c544, some c442, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p950 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked950 : lratChecker f950 p950 = .success := by decide +kernel
theorem unsat950 : Unsatisfiable (PosFin 31) f950 := by
  apply lratCheckerSound f950 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p950
  · intro a ha; simp [p950] at ha; subst a; trivial
  · exact checked950
theorem derived950 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c950 := by
  apply localUnsat_implies_entails f950 [c929, c911, c81, c939, c946, c138, c83, c202, c20, c78, c947, c948, c949, c891, c700, c544, c442] c950 unsat950 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c911 := derived911 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c939 := derived939 a h
  have h4 : Entails.eval a c946 := derived946 a h
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c947 := derived947 a h
  have h11 : Entails.eval a c948 := derived948 a h
  have h12 : Entails.eval a c949 := derived949 a h
  have h13 : Entails.eval a c891 := h 890 (by decide)
  have h14 : Entails.eval a c700 := h 699 (by decide)
  have h15 : Entails.eval a c544 := h 543 (by decide)
  have h16 : Entails.eval a c442 := h 441 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c951 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f951 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c25, some c950, some c929, some c83, some c20, some c78, some c949, some c891, some c867, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p951 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked951 : lratChecker f951 p951 = .success := by decide +kernel
theorem unsat951 : Unsatisfiable (PosFin 31) f951 := by
  apply lratCheckerSound f951 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p951
  · intro a ha; simp [p951] at ha; subst a; trivial
  · exact checked951
theorem derived951 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c951 := by
  apply localUnsat_implies_entails f951 [c81, c25, c950, c929, c83, c20, c78, c949, c891, c867] c951 unsat951 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c950 := derived950 a h
  have h3 : Entails.eval a c929 := derived929 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c949 := derived949 a h
  have h8 : Entails.eval a c891 := h 890 (by decide)
  have h9 : Entails.eval a c867 := h 866 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c952 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f952 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c950, some c81, some c25, some c951, some c138, some c48, some c171, some c264, some c454, some c310, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p952 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked952 : lratChecker f952 p952 = .success := by decide +kernel
theorem unsat952 : Unsatisfiable (PosFin 31) f952 := by
  apply lratCheckerSound f952 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p952
  · intro a ha; simp [p952] at ha; subst a; trivial
  · exact checked952
theorem derived952 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c952 := by
  apply localUnsat_implies_entails f952 [c950, c81, c25, c951, c138, c48, c171, c264, c454, c310] c952 unsat952 (by rfl) a
  have h0 : Entails.eval a c950 := derived950 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c951 := derived951 a h
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c171 := h 170 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c454 := h 453 (by decide)
  have h9 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c953 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f953 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c950, some c929, some c81, some c952, some c202, some c83, some c138, some c48, some c55, some c171, some c264, some c310, some c387, some c636, some c631, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p953 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked953 : lratChecker f953 p953 = .success := by decide +kernel
theorem unsat953 : Unsatisfiable (PosFin 31) f953 := by
  apply lratCheckerSound f953 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p953
  · intro a ha; simp [p953] at ha; subst a; trivial
  · exact checked953
theorem derived953 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c953 := by
  apply localUnsat_implies_entails f953 [c950, c929, c81, c952, c202, c83, c138, c48, c55, c171, c264, c310, c387, c636, c631] c953 unsat953 (by rfl) a
  have h0 : Entails.eval a c950 := derived950 a h
  have h1 : Entails.eval a c929 := derived929 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c952 := derived952 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c310 := h 309 (by decide)
  have h12 : Entails.eval a c387 := h 386 (by decide)
  have h13 : Entails.eval a c636 := h 635 (by decide)
  have h14 : Entails.eval a c631 := h 630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c954 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f954 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c953, some c950, some c929, some c81, some c83, some c138, some c48, some c4, some c171, some c847, some c264, some c285, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p954 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked954 : lratChecker f954 p954 = .success := by decide +kernel
theorem unsat954 : Unsatisfiable (PosFin 31) f954 := by
  apply lratCheckerSound f954 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p954
  · intro a ha; simp [p954] at ha; subst a; trivial
  · exact checked954
theorem derived954 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c954 := by
  apply localUnsat_implies_entails f954 [c953, c950, c929, c81, c83, c138, c48, c4, c171, c847, c264, c285] c954 unsat954 (by rfl) a
  have h0 : Entails.eval a c953 := derived953 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c847 := h 846 (by decide)
  have h10 : Entails.eval a c264 := h 263 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c955 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f955 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c950, some c81, some c953, some c954, some c202, some c25, some c230, some c358, some c327, some c276, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p955 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked955 : lratChecker f955 p955 = .success := by decide +kernel
theorem unsat955 : Unsatisfiable (PosFin 31) f955 := by
  apply lratCheckerSound f955 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p955
  · intro a ha; simp [p955] at ha; subst a; trivial
  · exact checked955
theorem derived955 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c955 := by
  apply localUnsat_implies_entails f955 [c950, c81, c953, c954, c202, c25, c230, c358, c327, c276] c955 unsat955 (by rfl) a
  have h0 : Entails.eval a c950 := derived950 a h
  have h1 : Entails.eval a c81 := h 80 (by decide)
  have h2 : Entails.eval a c953 := derived953 a h
  have h3 : Entails.eval a c954 := derived954 a h
  have h4 : Entails.eval a c202 := h 201 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c230 := h 229 (by decide)
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c327 := h 326 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c956 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f956 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c955, some c950, some c915, some c138, some c929, some c911, some c81, some c141, some c559, some c186, some c920, some c191, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p956 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked956 : lratChecker f956 p956 = .success := by decide +kernel
theorem unsat956 : Unsatisfiable (PosFin 31) f956 := by
  apply lratCheckerSound f956 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p956
  · intro a ha; simp [p956] at ha; subst a; trivial
  · exact checked956
theorem derived956 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c956 := by
  apply localUnsat_implies_entails f956 [c955, c950, c915, c138, c929, c911, c81, c141, c559, c186, c920, c191] c956 unsat956 (by rfl) a
  have h0 : Entails.eval a c955 := derived955 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c915 := derived915 a h
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c929 := derived929 a h
  have h5 : Entails.eval a c911 := derived911 a h
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c559 := h 558 (by decide)
  have h9 : Entails.eval a c186 := h 185 (by decide)
  have h10 : Entails.eval a c920 := derived920 a h
  have h11 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c957 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f957 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c955, some c950, some c929, some c956, some c86, some c205, some c303, some c264, some c501, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p957 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked957 : lratChecker f957 p957 = .success := by decide +kernel
theorem unsat957 : Unsatisfiable (PosFin 31) f957 := by
  apply lratCheckerSound f957 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p957
  · intro a ha; simp [p957] at ha; subst a; trivial
  · exact checked957
theorem derived957 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c957 := by
  apply localUnsat_implies_entails f957 [c955, c950, c929, c956, c86, c205, c303, c264, c501] c957 unsat957 (by rfl) a
  have h0 : Entails.eval a c955 := derived955 a h
  have h1 : Entails.eval a c950 := derived950 a h
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c956 := derived956 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c205 := h 204 (by decide)
  have h6 : Entails.eval a c303 := h 302 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c501 := h 500 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c958 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f958 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c957, some c955, some c950, some c929, some c81, some c86, some c205, some c264, some c501, some c66, some c71, some c219, some c116, some c745, some c590, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p958 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked958 : lratChecker f958 p958 = .success := by decide +kernel
theorem unsat958 : Unsatisfiable (PosFin 31) f958 := by
  apply lratCheckerSound f958 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p958
  · intro a ha; simp [p958] at ha; subst a; trivial
  · exact checked958
theorem derived958 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c958 := by
  apply localUnsat_implies_entails f958 [c957, c955, c950, c929, c81, c86, c205, c264, c501, c66, c71, c219, c116, c745, c590] c958 unsat958 (by rfl) a
  have h0 : Entails.eval a c957 := derived957 a h
  have h1 : Entails.eval a c955 := derived955 a h
  have h2 : Entails.eval a c950 := derived950 a h
  have h3 : Entails.eval a c929 := derived929 a h
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c501 := h 500 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c219 := h 218 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c745 := h 744 (by decide)
  have h14 : Entails.eval a c590 := h 589 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c959 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f959 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c955, some c205, some c958, some c957, some c81, some c90, some c71, some c219, some c227, some c745, some c640, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p959 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked959 : lratChecker f959 p959 = .success := by decide +kernel
theorem unsat959 : Unsatisfiable (PosFin 31) f959 := by
  apply lratCheckerSound f959 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p959
  · intro a ha; simp [p959] at ha; subst a; trivial
  · exact checked959
theorem derived959 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c959 := by
  apply localUnsat_implies_entails f959 [c929, c955, c205, c958, c957, c81, c90, c71, c219, c227, c745, c640] c959 unsat959 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c955 := derived955 a h
  have h2 : Entails.eval a c205 := h 204 (by decide)
  have h3 : Entails.eval a c958 := derived958 a h
  have h4 : Entails.eval a c957 := derived957 a h
  have h5 : Entails.eval a c81 := h 80 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  have h9 : Entails.eval a c227 := h 226 (by decide)
  have h10 : Entails.eval a c745 := h 744 (by decide)
  have h11 : Entails.eval a c640 := h 639 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c960 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f960 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c958, some c957, some c81, some c150, some c857, some c855, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p960 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked960 : lratChecker f960 p960 = .success := by decide +kernel
theorem unsat960 : Unsatisfiable (PosFin 31) f960 := by
  apply lratCheckerSound f960 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p960
  · intro a ha; simp [p960] at ha; subst a; trivial
  · exact checked960
theorem derived960 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c960 := by
  apply localUnsat_implies_entails f960 [c958, c957, c81, c150, c857, c855] c960 unsat960 (by rfl) a
  have h0 : Entails.eval a c958 := derived958 a h
  have h1 : Entails.eval a c957 := derived957 a h
  have h2 : Entails.eval a c81 := h 80 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c857 := h 856 (by decide)
  have h5 : Entails.eval a c855 := h 854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c961 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f961 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c960, some c138, some c83, some c842, some c202, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p961 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked961 : lratChecker f961 p961 = .success := by decide +kernel
theorem unsat961 : Unsatisfiable (PosFin 31) f961 := by
  apply lratCheckerSound f961 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p961
  · intro a ha; simp [p961] at ha; subst a; trivial
  · exact checked961
theorem derived961 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c961 := by
  apply localUnsat_implies_entails f961 [c929, c960, c138, c83, c842, c202] c961 unsat961 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c960 := derived960 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c842 := h 841 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c962 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f962 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c929, some c955, some c958, some c141, some c950, some c911, some c959, some c961, some c171, some c83, some c916, some c202, some c580, some c765, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p962 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked962 : lratChecker f962 p962 = .success := by decide +kernel
theorem unsat962 : Unsatisfiable (PosFin 31) f962 := by
  apply lratCheckerSound f962 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p962
  · intro a ha; simp [p962] at ha; subst a; trivial
  · exact checked962
theorem derived962 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c962 := by
  apply localUnsat_implies_entails f962 [c929, c955, c958, c141, c950, c911, c959, c961, c171, c83, c916, c202, c580, c765] c962 unsat962 (by rfl) a
  have h0 : Entails.eval a c929 := derived929 a h
  have h1 : Entails.eval a c955 := derived955 a h
  have h2 : Entails.eval a c958 := derived958 a h
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c950 := derived950 a h
  have h5 : Entails.eval a c911 := derived911 a h
  have h6 : Entails.eval a c959 := derived959 a h
  have h7 : Entails.eval a c961 := derived961 a h
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c916 := derived916 a h
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c580 := h 579 (by decide)
  have h13 : Entails.eval a c765 := h 764 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c963 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f963 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c81, some c911, some c929, some c955, some c957, some c958, some c141, some c962, some c387, some c78, some c147, some c90, some c506, some c698, some c733, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p963 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked963 : lratChecker f963 p963 = .success := by decide +kernel
theorem unsat963 : Unsatisfiable (PosFin 31) f963 := by
  apply lratCheckerSound f963 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p963
  · intro a ha; simp [p963] at ha; subst a; trivial
  · exact checked963
theorem derived963 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c963 := by
  apply localUnsat_implies_entails f963 [c81, c911, c929, c955, c957, c958, c141, c962, c387, c78, c147, c90, c506, c698, c733] c963 unsat963 (by rfl) a
  have h0 : Entails.eval a c81 := h 80 (by decide)
  have h1 : Entails.eval a c911 := derived911 a h
  have h2 : Entails.eval a c929 := derived929 a h
  have h3 : Entails.eval a c955 := derived955 a h
  have h4 : Entails.eval a c957 := derived957 a h
  have h5 : Entails.eval a c958 := derived958 a h
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c962 := derived962 a h
  have h8 : Entails.eval a c387 := h 386 (by decide)
  have h9 : Entails.eval a c78 := h 77 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c506 := h 505 (by decide)
  have h13 : Entails.eval a c698 := h 697 (by decide)
  have h14 : Entails.eval a c733 := h 732 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c964 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f964 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c963, some c141, some c720, some c212, some c422, some c222, some c460, some c628, some c424, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p964 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked964 : lratChecker f964 p964 = .success := by decide +kernel
theorem unsat964 : Unsatisfiable (PosFin 31) f964 := by
  apply lratCheckerSound f964 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p964
  · intro a ha; simp [p964] at ha; subst a; trivial
  · exact checked964
theorem derived964 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c964 := by
  apply localUnsat_implies_entails f964 [c963, c141, c720, c212, c422, c222, c460, c628, c424] c964 unsat964 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c720 := h 719 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c422 := h 421 (by decide)
  have h5 : Entails.eval a c222 := h 221 (by decide)
  have h6 : Entails.eval a c460 := h 459 (by decide)
  have h7 : Entails.eval a c628 := h 627 (by decide)
  have h8 : Entails.eval a c424 := h 423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c965 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨4, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f965 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c43, some c5, some c49, some c887, some c894, some c19, some c672, some c651, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p965 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked965 : lratChecker f965 p965 = .success := by decide +kernel
theorem unsat965 : Unsatisfiable (PosFin 31) f965 := by
  apply lratCheckerSound f965 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p965
  · intro a ha; simp [p965] at ha; subst a; trivial
  · exact checked965
theorem derived965 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c965 := by
  apply localUnsat_implies_entails f965 [c55, c43, c5, c49, c887, c894, c19, c672, c651] c965 unsat965 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c887 := h 886 (by decide)
  have h5 : Entails.eval a c894 := h 893 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c672 := h 671 (by decide)
  have h8 : Entails.eval a c651 := h 650 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c966 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f966 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c794, some c809, some c760, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p966 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked966 : lratChecker f966 p966 = .success := by decide +kernel
theorem unsat966 : Unsatisfiable (PosFin 31) f966 := by
  apply lratCheckerSound f966 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p966
  · intro a ha; simp [p966] at ha; subst a; trivial
  · exact checked966
theorem derived966 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c966 := by
  apply localUnsat_implies_entails f966 [c794, c809, c760] c966 unsat966 (by rfl) a
  have h0 : Entails.eval a c794 := h 793 (by decide)
  have h1 : Entails.eval a c809 := h 808 (by decide)
  have h2 : Entails.eval a c760 := h 759 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c967 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨1, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f967 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c322, some c272, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p967 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked967 : lratChecker f967 p967 = .success := by decide +kernel
theorem unsat967 : Unsatisfiable (PosFin 31) f967 := by
  apply lratCheckerSound f967 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p967
  · intro a ha; simp [p967] at ha; subst a; trivial
  · exact checked967
theorem derived967 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c967 := by
  apply localUnsat_implies_entails f967 [c322, c272] c967 unsat967 (by rfl) a
  have h0 : Entails.eval a c322 := h 321 (by decide)
  have h1 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c968 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨29, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f968 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c141, some c965, some c33, some c338, some c611, some c798, some c966, some c567, some c967, some c964, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p968 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked968 : lratChecker f968 p968 = .success := by decide +kernel
theorem unsat968 : Unsatisfiable (PosFin 31) f968 := by
  apply lratCheckerSound f968 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p968
  · intro a ha; simp [p968] at ha; subst a; trivial
  · exact checked968
theorem derived968 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c968 := by
  apply localUnsat_implies_entails f968 [c141, c965, c33, c338, c611, c798, c966, c567, c967, c964] c968 unsat968 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c965 := derived965 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c338 := h 337 (by decide)
  have h4 : Entails.eval a c611 := h 610 (by decide)
  have h5 : Entails.eval a c798 := h 797 (by decide)
  have h6 : Entails.eval a c966 := derived966 a h
  have h7 : Entails.eval a c567 := h 566 (by decide)
  have h8 : Entails.eval a c967 := derived967 a h
  have h9 : Entails.eval a c964 := derived964 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c969 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f969 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c545, some c967, some c223, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p969 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked969 : lratChecker f969 p969 = .success := by decide +kernel
theorem unsat969 : Unsatisfiable (PosFin 31) f969 := by
  apply lratCheckerSound f969 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p969
  · intro a ha; simp [p969] at ha; subst a; trivial
  · exact checked969
theorem derived969 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c969 := by
  apply localUnsat_implies_entails f969 [c545, c967, c223] c969 unsat969 (by rfl) a
  have h0 : Entails.eval a c545 := h 544 (by decide)
  have h1 : Entails.eval a c967 := derived967 a h
  have h2 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c970 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, false), (⟨1, by decide⟩, false), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f970 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c963, some c223, some c212, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p970 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked970 : lratChecker f970 p970 = .success := by decide +kernel
theorem unsat970 : Unsatisfiable (PosFin 31) f970 := by
  apply lratCheckerSound f970 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p970
  · intro a ha; simp [p970] at ha; subst a; trivial
  · exact checked970
theorem derived970 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c970 := by
  apply localUnsat_implies_entails f970 [c963, c223, c212] c970 unsat970 (by rfl) a
  have h0 : Entails.eval a c963 := derived963 a h
  have h1 : Entails.eval a c223 := h 222 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c971 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨4, by decide⟩, true), (⟨29, by decide⟩, true), (⟨27, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f971 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c445, some c424, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p971 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked971 : lratChecker f971 p971 = .success := by decide +kernel
theorem unsat971 : Unsatisfiable (PosFin 31) f971 := by
  apply lratCheckerSound f971 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p971
  · intro a ha; simp [p971] at ha; subst a; trivial
  · exact checked971
theorem derived971 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c971 := by
  apply localUnsat_implies_entails f971 [c445, c424] c971 unsat971 (by rfl) a
  have h0 : Entails.eval a c445 := h 444 (by decide)
  have h1 : Entails.eval a c424 := h 423 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c972 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f972 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c567, some c963, some c659, some c968, some c969, some c970, some c798, some c971, some c340, some c245, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p972 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked972 : lratChecker f972 p972 = .success := by decide +kernel
theorem unsat972 : Unsatisfiable (PosFin 31) f972 := by
  apply lratCheckerSound f972 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p972
  · intro a ha; simp [p972] at ha; subst a; trivial
  · exact checked972
theorem derived972 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c972 := by
  apply localUnsat_implies_entails f972 [c33, c567, c963, c659, c968, c969, c970, c798, c971, c340, c245] c972 unsat972 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c567 := h 566 (by decide)
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c659 := h 658 (by decide)
  have h4 : Entails.eval a c968 := derived968 a h
  have h5 : Entails.eval a c969 := derived969 a h
  have h6 : Entails.eval a c970 := derived970 a h
  have h7 : Entails.eval a c798 := h 797 (by decide)
  have h8 : Entails.eval a c971 := derived971 a h
  have h9 : Entails.eval a c340 := h 339 (by decide)
  have h10 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c973 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f973 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c798, some c276, some c807, some c262, some c257, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p973 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked973 : lratChecker f973 p973 = .success := by decide +kernel
theorem unsat973 : Unsatisfiable (PosFin 31) f973 := by
  apply lratCheckerSound f973 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p973
  · intro a ha; simp [p973] at ha; subst a; trivial
  · exact checked973
theorem derived973 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c973 := by
  apply localUnsat_implies_entails f973 [c798, c276, c807, c262, c257] c973 unsat973 (by rfl) a
  have h0 : Entails.eval a c798 := h 797 (by decide)
  have h1 : Entails.eval a c276 := h 275 (by decide)
  have h2 : Entails.eval a c807 := h 806 (by decide)
  have h3 : Entails.eval a c262 := h 261 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c974 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false), (⟨16, by decide⟩, false), (⟨2, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, false), (⟨1, by decide⟩, true), (⟨13, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f974 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c756, some c805, some c560, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p974 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked974 : lratChecker f974 p974 = .success := by decide +kernel
theorem unsat974 : Unsatisfiable (PosFin 31) f974 := by
  apply lratCheckerSound f974 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p974
  · intro a ha; simp [p974] at ha; subst a; trivial
  · exact checked974
theorem derived974 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c974 := by
  apply localUnsat_implies_entails f974 [c756, c805, c560] c974 unsat974 (by rfl) a
  have h0 : Entails.eval a c756 := h 755 (by decide)
  have h1 : Entails.eval a c805 := h 804 (by decide)
  have h2 : Entails.eval a c560 := h 559 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c975 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f975 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c972, some c973, some c966, some c276, some c33, some c340, some c974, some c381, some c760, some c119, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p975 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked975 : lratChecker f975 p975 = .success := by decide +kernel
theorem unsat975 : Unsatisfiable (PosFin 31) f975 := by
  apply lratCheckerSound f975 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p975
  · intro a ha; simp [p975] at ha; subst a; trivial
  · exact checked975
theorem derived975 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c975 := by
  apply localUnsat_implies_entails f975 [c972, c973, c966, c276, c33, c340, c974, c381, c760, c119] c975 unsat975 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c973 := derived973 a h
  have h2 : Entails.eval a c966 := derived966 a h
  have h3 : Entails.eval a c276 := h 275 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c340 := h 339 (by decide)
  have h6 : Entails.eval a c974 := derived974 a h
  have h7 : Entails.eval a c381 := h 380 (by decide)
  have h8 : Entails.eval a c760 := h 759 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c976 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f976 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c972, some c33, some c973, some c966, some c276, some c338, some c975, some c348, some c739, some c755, some c742, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p976 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked976 : lratChecker f976 p976 = .success := by decide +kernel
theorem unsat976 : Unsatisfiable (PosFin 31) f976 := by
  apply lratCheckerSound f976 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p976
  · intro a ha; simp [p976] at ha; subst a; trivial
  · exact checked976
theorem derived976 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c976 := by
  apply localUnsat_implies_entails f976 [c972, c33, c973, c966, c276, c338, c975, c348, c739, c755, c742] c976 unsat976 (by rfl) a
  have h0 : Entails.eval a c972 := derived972 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c973 := derived973 a h
  have h3 : Entails.eval a c966 := derived966 a h
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c338 := h 337 (by decide)
  have h6 : Entails.eval a c975 := derived975 a h
  have h7 : Entails.eval a c348 := h 347 (by decide)
  have h8 : Entails.eval a c739 := h 738 (by decide)
  have h9 : Entails.eval a c755 := h 754 (by decide)
  have h10 : Entails.eval a c742 := h 741 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c977 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f977 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c972, some c976, some c70, some c611, some c699, some c35, some c276, some c739, some c305, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p977 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked977 : lratChecker f977 p977 = .success := by decide +kernel
theorem unsat977 : Unsatisfiable (PosFin 31) f977 := by
  apply lratCheckerSound f977 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p977
  · intro a ha; simp [p977] at ha; subst a; trivial
  · exact checked977
theorem derived977 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c977 := by
  apply localUnsat_implies_entails f977 [c33, c972, c976, c70, c611, c699, c35, c276, c739, c305] c977 unsat977 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c972 := derived972 a h
  have h2 : Entails.eval a c976 := derived976 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c611 := h 610 (by decide)
  have h5 : Entails.eval a c699 := h 698 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c739 := h 738 (by decide)
  have h9 : Entails.eval a c305 := h 304 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c978 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨18, by decide⟩, false), (⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f978 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c43, some c55, some c276, some c309, some c769, some c34, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p978 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked978 : lratChecker f978 p978 = .success := by decide +kernel
theorem unsat978 : Unsatisfiable (PosFin 31) f978 := by
  apply lratCheckerSound f978 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p978
  · intro a ha; simp [p978] at ha; subst a; trivial
  · exact checked978
theorem derived978 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c978 := by
  apply localUnsat_implies_entails f978 [c43, c55, c276, c309, c769, c34] c978 unsat978 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c276 := h 275 (by decide)
  have h3 : Entails.eval a c309 := h 308 (by decide)
  have h4 : Entails.eval a c769 := h 768 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c979 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f979 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c43, some c978, some c263, some c611, some c625, some c256, some c767, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p979 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked979 : lratChecker f979 p979 = .success := by decide +kernel
theorem unsat979 : Unsatisfiable (PosFin 31) f979 := by
  apply lratCheckerSound f979 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p979
  · intro a ha; simp [p979] at ha; subst a; trivial
  · exact checked979
theorem derived979 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c979 := by
  apply localUnsat_implies_entails f979 [c43, c978, c263, c611, c625, c256, c767] c979 unsat979 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c978 := derived978 a h
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c611 := h 610 (by decide)
  have h4 : Entails.eval a c625 := h 624 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c767 := h 766 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c980 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f980 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c979, some c55, some c49, some c43, some c263, some c256, some c807, some c19, some c270, some c72, some c73, some c157, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p980 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked980 : lratChecker f980 p980 = .success := by decide +kernel
theorem unsat980 : Unsatisfiable (PosFin 31) f980 := by
  apply lratCheckerSound f980 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p980
  · intro a ha; simp [p980] at ha; subst a; trivial
  · exact checked980
theorem derived980 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c980 := by
  apply localUnsat_implies_entails f980 [c979, c55, c49, c43, c263, c256, c807, c19, c270, c72, c73, c157] c980 unsat980 (by rfl) a
  have h0 : Entails.eval a c979 := derived979 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c807 := h 806 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c73 := h 72 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c981 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f981 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c55, some c49, some c43, some c979, some c980, some c276, some c309, some c19, some c848, some c898, some c563, some c216, some c450, some c638, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p981 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked981 : lratChecker f981 p981 = .success := by decide +kernel
theorem unsat981 : Unsatisfiable (PosFin 31) f981 := by
  apply lratCheckerSound f981 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p981
  · intro a ha; simp [p981] at ha; subst a; trivial
  · exact checked981
theorem derived981 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c981 := by
  apply localUnsat_implies_entails f981 [c55, c49, c43, c979, c980, c276, c309, c19, c848, c898, c563, c216, c450, c638] c981 unsat981 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c979 := derived979 a h
  have h4 : Entails.eval a c980 := derived980 a h
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c848 := h 847 (by decide)
  have h9 : Entails.eval a c898 := h 897 (by decide)
  have h10 : Entails.eval a c563 := h 562 (by decide)
  have h11 : Entails.eval a c216 := h 215 (by decide)
  have h12 : Entails.eval a c450 := h 449 (by decide)
  have h13 : Entails.eval a c638 := h 637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c982 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨7, by decide⟩, true), (⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f982 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c977, some c55, some c43, some c981, some c894, some c816, some c887, some c804, some c963, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p982 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked982 : lratChecker f982 p982 = .success := by decide +kernel
theorem unsat982 : Unsatisfiable (PosFin 31) f982 := by
  apply lratCheckerSound f982 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p982
  · intro a ha; simp [p982] at ha; subst a; trivial
  · exact checked982
theorem derived982 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c982 := by
  apply localUnsat_implies_entails f982 [c977, c55, c43, c981, c894, c816, c887, c804, c963] c982 unsat982 (by rfl) a
  have h0 : Entails.eval a c977 := derived977 a h
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c981 := derived981 a h
  have h4 : Entails.eval a c894 := h 893 (by decide)
  have h5 : Entails.eval a c816 := h 815 (by decide)
  have h6 : Entails.eval a c887 := h 886 (by decide)
  have h7 : Entails.eval a c804 := h 803 (by decide)
  have h8 : Entails.eval a c963 := derived963 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c983 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f983 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c141, some c55, some c172, some c43, some c263, some c276, some c309, some c34, some c706, some c874, some c871, some c19, some c659, some c662, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p983 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked983 : lratChecker f983 p983 = .success := by decide +kernel
theorem unsat983 : Unsatisfiable (PosFin 31) f983 := by
  apply lratCheckerSound f983 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p983
  · intro a ha; simp [p983] at ha; subst a; trivial
  · exact checked983
theorem derived983 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c983 := by
  apply localUnsat_implies_entails f983 [c141, c55, c172, c43, c263, c276, c309, c34, c706, c874, c871, c19, c659, c662] c983 unsat983 (by rfl) a
  have h0 : Entails.eval a c141 := h 140 (by decide)
  have h1 : Entails.eval a c55 := h 54 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c706 := h 705 (by decide)
  have h9 : Entails.eval a c874 := h 873 (by decide)
  have h10 : Entails.eval a c871 := h 870 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c659 := h 658 (by decide)
  have h13 : Entails.eval a c662 := h 661 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c984 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f984 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c982, some c84, some c141, some c983, some c145, some c48, some c33, some c659, some c751, some c963, some c853, some c827, some c89, some c157, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p984 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked984 : lratChecker f984 p984 = .success := by decide +kernel
theorem unsat984 : Unsatisfiable (PosFin 31) f984 := by
  apply lratCheckerSound f984 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p984
  · intro a ha; simp [p984] at ha; subst a; trivial
  · exact checked984
theorem derived984 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c984 := by
  apply localUnsat_implies_entails f984 [c982, c84, c141, c983, c145, c48, c33, c659, c751, c963, c853, c827, c89, c157] c984 unsat984 (by rfl) a
  have h0 : Entails.eval a c982 := derived982 a h
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c983 := derived983 a h
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c659 := h 658 (by decide)
  have h8 : Entails.eval a c751 := h 750 (by decide)
  have h9 : Entails.eval a c963 := derived963 a h
  have h10 : Entails.eval a c853 := h 852 (by decide)
  have h11 : Entails.eval a c827 := h 826 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c985 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨20, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f985 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c963, some c647, some c842, some c157, some c712, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p985 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked985 : lratChecker f985 p985 = .success := by decide +kernel
theorem unsat985 : Unsatisfiable (PosFin 31) f985 := by
  apply lratCheckerSound f985 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p985
  · intro a ha; simp [p985] at ha; subst a; trivial
  · exact checked985
theorem derived985 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c985 := by
  apply localUnsat_implies_entails f985 [c84, c963, c647, c842, c157, c712] c985 unsat985 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c647 := h 646 (by decide)
  have h3 : Entails.eval a c842 := h 841 (by decide)
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c712 := h 711 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c986 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨1, by decide⟩, true), (⟨20, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨26, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f986 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c48, some c985, some c887, some c50, some c152, some c673, some c259, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p986 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked986 : lratChecker f986 p986 = .success := by decide +kernel
theorem unsat986 : Unsatisfiable (PosFin 31) f986 := by
  apply lratCheckerSound f986 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p986
  · intro a ha; simp [p986] at ha; subst a; trivial
  · exact checked986
theorem derived986 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c986 := by
  apply localUnsat_implies_entails f986 [c84, c48, c985, c887, c50, c152, c673, c259] c986 unsat986 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c48 := h 47 (by decide)
  have h2 : Entails.eval a c985 := derived985 a h
  have h3 : Entails.eval a c887 := h 886 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c673 := h 672 (by decide)
  have h7 : Entails.eval a c259 := h 258 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c987 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f987 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c982, some c141, some c983, some c145, some c48, some c84, some c984, some c986, some c262, some c276, some c853, some c20, some c152, some c184, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p987 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked987 : lratChecker f987 p987 = .success := by decide +kernel
theorem unsat987 : Unsatisfiable (PosFin 31) f987 := by
  apply lratCheckerSound f987 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p987
  · intro a ha; simp [p987] at ha; subst a; trivial
  · exact checked987
theorem derived987 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c987 := by
  apply localUnsat_implies_entails f987 [c982, c141, c983, c145, c48, c84, c984, c986, c262, c276, c853, c20, c152, c184] c987 unsat987 (by rfl) a
  have h0 : Entails.eval a c982 := derived982 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c145 := h 144 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c984 := derived984 a h
  have h7 : Entails.eval a c986 := derived986 a h
  have h8 : Entails.eval a c262 := h 261 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c853 := h 852 (by decide)
  have h11 : Entails.eval a c20 := h 19 (by decide)
  have h12 : Entails.eval a c152 := h 151 (by decide)
  have h13 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c988 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true), (⟨20, by decide⟩, false), (⟨21, by decide⟩, true), (⟨25, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f988 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c853, some c858, some c886, some c655, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p988 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked988 : lratChecker f988 p988 = .success := by decide +kernel
theorem unsat988 : Unsatisfiable (PosFin 31) f988 := by
  apply lratCheckerSound f988 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p988
  · intro a ha; simp [p988] at ha; subst a; trivial
  · exact checked988
theorem derived988 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c988 := by
  apply localUnsat_implies_entails f988 [c33, c853, c858, c886, c655] c988 unsat988 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c853 := h 852 (by decide)
  have h2 : Entails.eval a c858 := h 857 (by decide)
  have h3 : Entails.eval a c886 := h 885 (by decide)
  have h4 : Entails.eval a c655 := h 654 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c989 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f989 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c982, some c141, some c983, some c33, some c48, some c145, some c987, some c91, some c988, some c276, some c338, some c257, some c706, some c739, some c351, some c251, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p989 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked989 : lratChecker f989 p989 = .success := by decide +kernel
theorem unsat989 : Unsatisfiable (PosFin 31) f989 := by
  apply lratCheckerSound f989 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p989
  · intro a ha; simp [p989] at ha; subst a; trivial
  · exact checked989
theorem derived989 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c989 := by
  apply localUnsat_implies_entails f989 [c982, c141, c983, c33, c48, c145, c987, c91, c988, c276, c338, c257, c706, c739, c351, c251] c989 unsat989 (by rfl) a
  have h0 : Entails.eval a c982 := derived982 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c983 := derived983 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c145 := h 144 (by decide)
  have h6 : Entails.eval a c987 := derived987 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c988 := derived988 a h
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c338 := h 337 (by decide)
  have h11 : Entails.eval a c257 := h 256 (by decide)
  have h12 : Entails.eval a c706 := h 705 (by decide)
  have h13 : Entails.eval a c739 := h 738 (by decide)
  have h14 : Entails.eval a c351 := h 350 (by decide)
  have h15 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c990 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨15, by decide⟩, true), (⟨26, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f990 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c989, some c39, some c57, some c706, some c875, some c35, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p990 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked990 : lratChecker f990 p990 = .success := by decide +kernel
theorem unsat990 : Unsatisfiable (PosFin 31) f990 := by
  apply lratCheckerSound f990 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p990
  · intro a ha; simp [p990] at ha; subst a; trivial
  · exact checked990
theorem derived990 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c990 := by
  apply localUnsat_implies_entails f990 [c989, c39, c57, c706, c875, c35] c990 unsat990 (by rfl) a
  have h0 : Entails.eval a c989 := derived989 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c706 := h 705 (by decide)
  have h4 : Entails.eval a c875 := h 874 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c991 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨20, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f991 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c80, some c989, some c39, some c141, some c91, some c57, some c990, some c276, some c856, some c20, some c345, some c815, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p991 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked991 : lratChecker f991 p991 = .success := by decide +kernel
theorem unsat991 : Unsatisfiable (PosFin 31) f991 := by
  apply lratCheckerSound f991 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p991
  · intro a ha; simp [p991] at ha; subst a; trivial
  · exact checked991
theorem derived991 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c991 := by
  apply localUnsat_implies_entails f991 [c80, c989, c39, c141, c91, c57, c990, c276, c856, c20, c345, c815] c991 unsat991 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c989 := derived989 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c990 := derived990 a h
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c856 := h 855 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c345 := h 344 (by decide)
  have h11 : Entails.eval a c815 := h 814 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c992 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨1, by decide⟩, false), (⟨26, by decide⟩, true), (⟨9, by decide⟩, false), (⟨27, by decide⟩, true), (⟨21, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f992 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c567, some c751, some c569, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p992 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked992 : lratChecker f992 p992 = .success := by decide +kernel
theorem unsat992 : Unsatisfiable (PosFin 31) f992 := by
  apply lratCheckerSound f992 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p992
  · intro a ha; simp [p992] at ha; subst a; trivial
  · exact checked992
theorem derived992 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c992 := by
  apply localUnsat_implies_entails f992 [c567, c751, c569] c992 unsat992 (by rfl) a
  have h0 : Entails.eval a c567 := h 566 (by decide)
  have h1 : Entails.eval a c751 := h 750 (by decide)
  have h2 : Entails.eval a c569 := h 568 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c993 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f993 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c989, some c39, some c80, some c991, some c146, some c182, some c257, some c20, some c1, some c992, some c743, some c357, some c822, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p993 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked993 : lratChecker f993 p993 = .success := by decide +kernel
theorem unsat993 : Unsatisfiable (PosFin 31) f993 := by
  apply lratCheckerSound f993 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p993
  · intro a ha; simp [p993] at ha; subst a; trivial
  · exact checked993
theorem derived993 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c993 := by
  apply localUnsat_implies_entails f993 [c989, c39, c80, c991, c146, c182, c257, c20, c1, c992, c743, c357, c822] c993 unsat993 (by rfl) a
  have h0 : Entails.eval a c989 := derived989 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c991 := derived991 a h
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c182 := h 181 (by decide)
  have h6 : Entails.eval a c257 := h 256 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c992 := derived992 a h
  have h10 : Entails.eval a c743 := h 742 (by decide)
  have h11 : Entails.eval a c357 := h 356 (by decide)
  have h12 : Entails.eval a c822 := h 821 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c994 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f994 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c989, some c39, some c56, some c799, some c611, some c795, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p994 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked994 : lratChecker f994 p994 = .success := by decide +kernel
theorem unsat994 : Unsatisfiable (PosFin 31) f994 := by
  apply lratCheckerSound f994 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p994
  · intro a ha; simp [p994] at ha; subst a; trivial
  · exact checked994
theorem derived994 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c994 := by
  apply localUnsat_implies_entails f994 [c989, c39, c56, c799, c611, c795] c994 unsat994 (by rfl) a
  have h0 : Entails.eval a c989 := derived989 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c799 := h 798 (by decide)
  have h4 : Entails.eval a c611 := h 610 (by decide)
  have h5 : Entails.eval a c795 := h 794 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c995 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f995 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c145, some c989, some c39, some c993, some c56, some c994, some c276, some c19, some c990, some c744, some c659, some c373, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p995 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked995 : lratChecker f995 p995 = .success := by decide +kernel
theorem unsat995 : Unsatisfiable (PosFin 31) f995 := by
  apply lratCheckerSound f995 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p995
  · intro a ha; simp [p995] at ha; subst a; trivial
  · exact checked995
theorem derived995 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c995 := by
  apply localUnsat_implies_entails f995 [c145, c989, c39, c993, c56, c994, c276, c19, c990, c744, c659, c373] c995 unsat995 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c989 := derived989 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c993 := derived993 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c994 := derived994 a h
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c990 := derived990 a h
  have h9 : Entails.eval a c744 := h 743 (by decide)
  have h10 : Entails.eval a c659 := h 658 (by decide)
  have h11 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c996 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨26, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f996 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c993, some c995, some c84, some c989, some c39, some c56, some c276, some c338, some c706, some c713, some c716, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p996 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked996 : lratChecker f996 p996 = .success := by decide +kernel
theorem unsat996 : Unsatisfiable (PosFin 31) f996 := by
  apply lratCheckerSound f996 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p996
  · intro a ha; simp [p996] at ha; subst a; trivial
  · exact checked996
theorem derived996 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c996 := by
  apply localUnsat_implies_entails f996 [c993, c995, c84, c989, c39, c56, c276, c338, c706, c713, c716] c996 unsat996 (by rfl) a
  have h0 : Entails.eval a c993 := derived993 a h
  have h1 : Entails.eval a c995 := derived995 a h
  have h2 : Entails.eval a c84 := h 83 (by decide)
  have h3 : Entails.eval a c989 := derived989 a h
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c338 := h 337 (by decide)
  have h8 : Entails.eval a c706 := h 705 (by decide)
  have h9 : Entails.eval a c713 := h 712 (by decide)
  have h10 : Entails.eval a c716 := h 715 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c997 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f997 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c989, some c39, some c993, some c56, some c145, some c995, some c996, some c20, some c659, some c823, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p997 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked997 : lratChecker f997 p997 = .success := by decide +kernel
theorem unsat997 : Unsatisfiable (PosFin 31) f997 := by
  apply lratCheckerSound f997 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p997
  · intro a ha; simp [p997] at ha; subst a; trivial
  · exact checked997
theorem derived997 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c997 := by
  apply localUnsat_implies_entails f997 [c989, c39, c993, c56, c145, c995, c996, c20, c659, c823] c997 unsat997 (by rfl) a
  have h0 : Entails.eval a c989 := derived989 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c993 := derived993 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c995 := derived995 a h
  have h6 : Entails.eval a c996 := derived996 a h
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c659 := h 658 (by decide)
  have h9 : Entails.eval a c823 := h 822 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c998 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f998 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c989, some c39, some c993, some c56, some c997, some c141, some c994, some c276, some c338, some c262, some c19, some c851, some c894, some c816, some c739, some c250, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p998 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked998 : lratChecker f998 p998 = .success := by decide +kernel
theorem unsat998 : Unsatisfiable (PosFin 31) f998 := by
  apply lratCheckerSound f998 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p998
  · intro a ha; simp [p998] at ha; subst a; trivial
  · exact checked998
theorem derived998 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c998 := by
  apply localUnsat_implies_entails f998 [c989, c39, c993, c56, c997, c141, c994, c276, c338, c262, c19, c851, c894, c816, c739, c250] c998 unsat998 (by rfl) a
  have h0 : Entails.eval a c989 := derived989 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c993 := derived993 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c997 := derived997 a h
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c994 := derived994 a h
  have h7 : Entails.eval a c276 := h 275 (by decide)
  have h8 : Entails.eval a c338 := h 337 (by decide)
  have h9 : Entails.eval a c262 := h 261 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c851 := h 850 (by decide)
  have h12 : Entails.eval a c894 := h 893 (by decide)
  have h13 : Entails.eval a c816 := h 815 (by decide)
  have h14 : Entails.eval a c739 := h 738 (by decide)
  have h15 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c999 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f999 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c998, some c43, some c989, some c39, some c276, some c19, some c309, some c56, some c55, some c769, some c894, some c332, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p999 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked999 : lratChecker f999 p999 = .success := by decide +kernel
theorem unsat999 : Unsatisfiable (PosFin 31) f999 := by
  apply lratCheckerSound f999 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p999
  · intro a ha; simp [p999] at ha; subst a; trivial
  · exact checked999
theorem derived999 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c999 := by
  apply localUnsat_implies_entails f999 [c998, c43, c989, c39, c276, c19, c309, c56, c55, c769, c894, c332] c999 unsat999 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c989 := derived989 a h
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c276 := h 275 (by decide)
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c309 := h 308 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c769 := h 768 (by decide)
  have h10 : Entails.eval a c894 := h 893 (by decide)
  have h11 : Entails.eval a c332 := h 331 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1000 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1000 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c989, some c39, some c998, some c43, some c56, some c276, some c19, some c999, some c141, some c823, some c659, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1000 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1000 : lratChecker f1000 p1000 = .success := by decide +kernel
theorem unsat1000 : Unsatisfiable (PosFin 31) f1000 := by
  apply lratCheckerSound f1000 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1000
  · intro a ha; simp [p1000] at ha; subst a; trivial
  · exact checked1000
theorem derived1000 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1000 := by
  apply localUnsat_implies_entails f1000 [c989, c39, c998, c43, c56, c276, c19, c999, c141, c823, c659] c1000 unsat1000 (by rfl) a
  have h0 : Entails.eval a c989 := derived989 a h
  have h1 : Entails.eval a c39 := h 38 (by decide)
  have h2 : Entails.eval a c998 := derived998 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c276 := h 275 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c999 := derived999 a h
  have h8 : Entails.eval a c141 := h 140 (by decide)
  have h9 : Entails.eval a c823 := h 822 (by decide)
  have h10 : Entails.eval a c659 := h 658 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1001 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨14, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1001 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c998, some c43, some c1000, some c263, some c994, some c172, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1001 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1001 : lratChecker f1001 p1001 = .success := by decide +kernel
theorem unsat1001 : Unsatisfiable (PosFin 31) f1001 := by
  apply lratCheckerSound f1001 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1001
  · intro a ha; simp [p1001] at ha; subst a; trivial
  · exact checked1001
theorem derived1001 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1001 := by
  apply localUnsat_implies_entails f1001 [c998, c43, c1000, c263, c994, c172] c1001 unsat1001 (by rfl) a
  have h0 : Entails.eval a c998 := derived998 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c1000 := derived1000 a h
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c994 := derived994 a h
  have h5 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1002 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1002 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c263, some c172, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true))]
def p1002 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1002 : lratChecker f1002 p1002 = .success := by decide +kernel
theorem unsat1002 : Unsatisfiable (PosFin 31) f1002 := by
  apply lratCheckerSound f1002 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1002
  · intro a ha; simp [p1002] at ha; subst a; trivial
  · exact checked1002
theorem derived1002 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1002 := by
  apply localUnsat_implies_entails f1002 [c263, c172] c1002 unsat1002 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived1002

end CochromaticTwenty.Certificates.Z12Direct_5_8_13
