import MerLeanExperiment.Certificates.Z12Direct_5_8_7.Steps0400_0499

/-! Generated from the actual pinned z12direct_5_8_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1245 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1243, some c1058, some c28, some c213, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1245 : lratChecker f1245 p1245 = .success := by decide +kernel
theorem unsat1245 : Unsatisfiable (PosFin 31) f1245 := by
  apply lratCheckerSound f1245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1245
  · intro a ha; simp [p1245] at ha; subst a; trivial
  · exact checked1245
theorem derived1245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1245 := by
  apply localUnsat_implies_entails f1245 [c1243, c1058, c28, c213] c1245 unsat1245 (by rfl) a
  have h0 : Entails.eval a c1243 := derived1243 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1246 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1243, some c1216, some c1244, some c61, some c1245, some c20, some c21, some c180, some c81, some c86, some c1016, some c477, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1246 : lratChecker f1246 p1246 = .success := by decide +kernel
theorem unsat1246 : Unsatisfiable (PosFin 31) f1246 := by
  apply lratCheckerSound f1246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1246
  · intro a ha; simp [p1246] at ha; subst a; trivial
  · exact checked1246
theorem derived1246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1246 := by
  apply localUnsat_implies_entails f1246 [c1184, c1243, c1216, c1244, c61, c1245, c20, c21, c180, c81, c86, c1016, c477] c1246 unsat1246 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1243 := derived1243 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c1244 := derived1244 a h
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c1245 := derived1245 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c180 := h 179 (by decide)
  have h9 : Entails.eval a c81 := h 80 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c1016 := derived1016 a h
  have h12 : Entails.eval a c477 := h 476 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1247 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1243, some c1216, some c67, some c1056, some c6, some c269, some c232, some c20, some c21, some c1039, some c441, some c471, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1247 : lratChecker f1247 p1247 = .success := by decide +kernel
theorem unsat1247 : Unsatisfiable (PosFin 31) f1247 := by
  apply lratCheckerSound f1247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1247
  · intro a ha; simp [p1247] at ha; subst a; trivial
  · exact checked1247
theorem derived1247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1247 := by
  apply localUnsat_implies_entails f1247 [c1184, c1243, c1216, c67, c1056, c6, c269, c232, c20, c21, c1039, c441, c471] c1247 unsat1247 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1243 := derived1243 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c1056 := derived1056 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c1039 := derived1039 a h
  have h11 : Entails.eval a c441 := h 440 (by decide)
  have h12 : Entails.eval a c471 := h 470 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1248 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1247, some c1246, some c1243, some c1216, some c1059, some c1061, some c1060, some c8, some c187, some c1035, some c103, some c232, some c1071, some c499, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1248 : lratChecker f1248 p1248 = .success := by decide +kernel
theorem unsat1248 : Unsatisfiable (PosFin 31) f1248 := by
  apply lratCheckerSound f1248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1248
  · intro a ha; simp [p1248] at ha; subst a; trivial
  · exact checked1248
theorem derived1248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1248 := by
  apply localUnsat_implies_entails f1248 [c1184, c1247, c1246, c1243, c1216, c1059, c1061, c1060, c8, c187, c1035, c103, c232, c1071, c499] c1248 unsat1248 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1247 := derived1247 a h
  have h2 : Entails.eval a c1246 := derived1246 a h
  have h3 : Entails.eval a c1243 := derived1243 a h
  have h4 : Entails.eval a c1216 := derived1216 a h
  have h5 : Entails.eval a c1059 := derived1059 a h
  have h6 : Entails.eval a c1061 := derived1061 a h
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c1035 := derived1035 a h
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c232 := h 231 (by decide)
  have h13 : Entails.eval a c1071 := derived1071 a h
  have h14 : Entails.eval a c499 := h 498 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1249 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1243, some c1247, some c1246, some c1248, some c1058, some c28, some c1035, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1249 : lratChecker f1249 p1249 = .success := by decide +kernel
theorem unsat1249 : Unsatisfiable (PosFin 31) f1249 := by
  apply lratCheckerSound f1249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1249
  · intro a ha; simp [p1249] at ha; subst a; trivial
  · exact checked1249
theorem derived1249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1249 := by
  apply localUnsat_implies_entails f1249 [c1243, c1247, c1246, c1248, c1058, c28, c1035] c1249 unsat1249 (by rfl) a
  have h0 : Entails.eval a c1243 := derived1243 a h
  have h1 : Entails.eval a c1247 := derived1247 a h
  have h2 : Entails.eval a c1246 := derived1246 a h
  have h3 : Entails.eval a c1248 := derived1248 a h
  have h4 : Entails.eval a c1058 := derived1058 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c1035 := derived1035 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1250 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1249, some c1243, some c1216, some c28, some c1037, some c1035, some c750, some c481, some c1075, some c645, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1250 : lratChecker f1250 p1250 = .success := by decide +kernel
theorem unsat1250 : Unsatisfiable (PosFin 31) f1250 := by
  apply lratCheckerSound f1250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1250
  · intro a ha; simp [p1250] at ha; subst a; trivial
  · exact checked1250
theorem derived1250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1250 := by
  apply localUnsat_implies_entails f1250 [c1184, c1249, c1243, c1216, c28, c1037, c1035, c750, c481, c1075, c645] c1250 unsat1250 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1249 := derived1249 a h
  have h2 : Entails.eval a c1243 := derived1243 a h
  have h3 : Entails.eval a c1216 := derived1216 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c1037 := derived1037 a h
  have h6 : Entails.eval a c1035 := derived1035 a h
  have h7 : Entails.eval a c750 := derived750 a h
  have h8 : Entails.eval a c481 := h 480 (by decide)
  have h9 : Entails.eval a c1075 := derived1075 a h
  have h10 : Entails.eval a c645 := h 644 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1251 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1250, some c1061, some c1059, some c1249, some c1037, some c1035, some c750, some c1200, some c1084, some c1075, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1251 : lratChecker f1251 p1251 = .success := by decide +kernel
theorem unsat1251 : Unsatisfiable (PosFin 31) f1251 := by
  apply lratCheckerSound f1251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1251
  · intro a ha; simp [p1251] at ha; subst a; trivial
  · exact checked1251
theorem derived1251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1251 := by
  apply localUnsat_implies_entails f1251 [c1184, c1250, c1061, c1059, c1249, c1037, c1035, c750, c1200, c1084, c1075] c1251 unsat1251 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1250 := derived1250 a h
  have h2 : Entails.eval a c1061 := derived1061 a h
  have h3 : Entails.eval a c1059 := derived1059 a h
  have h4 : Entails.eval a c1249 := derived1249 a h
  have h5 : Entails.eval a c1037 := derived1037 a h
  have h6 : Entails.eval a c1035 := derived1035 a h
  have h7 : Entails.eval a c750 := derived750 a h
  have h8 : Entails.eval a c1200 := derived1200 a h
  have h9 : Entails.eval a c1084 := derived1084 a h
  have h10 : Entails.eval a c1075 := derived1075 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1252 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1249, some c1243, some c1216, some c1250, some c1059, some c1061, some c1251, some c232, some c21, some c750, some c233, some c1084, some c80, some c1075, some c631, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1252 : lratChecker f1252 p1252 = .success := by decide +kernel
theorem unsat1252 : Unsatisfiable (PosFin 31) f1252 := by
  apply lratCheckerSound f1252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1252
  · intro a ha; simp [p1252] at ha; subst a; trivial
  · exact checked1252
theorem derived1252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1252 := by
  apply localUnsat_implies_entails f1252 [c1184, c1249, c1243, c1216, c1250, c1059, c1061, c1251, c232, c21, c750, c233, c1084, c80, c1075, c631] c1252 unsat1252 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1249 := derived1249 a h
  have h2 : Entails.eval a c1243 := derived1243 a h
  have h3 : Entails.eval a c1216 := derived1216 a h
  have h4 : Entails.eval a c1250 := derived1250 a h
  have h5 : Entails.eval a c1059 := derived1059 a h
  have h6 : Entails.eval a c1061 := derived1061 a h
  have h7 : Entails.eval a c1251 := derived1251 a h
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c750 := derived750 a h
  have h11 : Entails.eval a c233 := h 232 (by decide)
  have h12 : Entails.eval a c1084 := derived1084 a h
  have h13 : Entails.eval a c80 := h 79 (by decide)
  have h14 : Entails.eval a c1075 := derived1075 a h
  have h15 : Entails.eval a c631 := h 630 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1253 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1243, some c1216, some c1252, some c67, some c1056, some c6, some c269, some c232, some c35, some c1038, some c1073, some c244, some c1071, some c509, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1253 : lratChecker f1253 p1253 = .success := by decide +kernel
theorem unsat1253 : Unsatisfiable (PosFin 31) f1253 := by
  apply lratCheckerSound f1253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1253
  · intro a ha; simp [p1253] at ha; subst a; trivial
  · exact checked1253
theorem derived1253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1253 := by
  apply localUnsat_implies_entails f1253 [c1184, c1243, c1216, c1252, c67, c1056, c6, c269, c232, c35, c1038, c1073, c244, c1071, c509] c1253 unsat1253 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1243 := derived1243 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c1252 := derived1252 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c1056 := derived1056 a h
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c232 := h 231 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c1038 := derived1038 a h
  have h11 : Entails.eval a c1073 := derived1073 a h
  have h12 : Entails.eval a c244 := h 243 (by decide)
  have h13 : Entails.eval a c1071 := derived1071 a h
  have h14 : Entails.eval a c509 := h 508 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1254 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1243, some c1249, some c1253, some c78, some c1037, some c232, some c28, some c21, some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1254 : lratChecker f1254 p1254 = .success := by decide +kernel
theorem unsat1254 : Unsatisfiable (PosFin 31) f1254 := by
  apply lratCheckerSound f1254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1254
  · intro a ha; simp [p1254] at ha; subst a; trivial
  · exact checked1254
theorem derived1254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1254 := by
  apply localUnsat_implies_entails f1254 [c1184, c1216, c1243, c1249, c1253, c78, c1037, c232, c28, c21] c1254 unsat1254 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1243 := derived1243 a h
  have h3 : Entails.eval a c1249 := derived1249 a h
  have h4 : Entails.eval a c1253 := derived1253 a h
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c1037 := derived1037 a h
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1255 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1184, some c21, some c184, some c64, some c78, some c228, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1255 : lratChecker f1255 p1255 = .success := by decide +kernel
theorem unsat1255 : Unsatisfiable (PosFin 31) f1255 := by
  apply lratCheckerSound f1255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1255
  · intro a ha; simp [p1255] at ha; subst a; trivial
  · exact checked1255
theorem derived1255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1255 := by
  apply localUnsat_implies_entails f1255 [c1254, c1184, c21, c184, c64, c78, c228] c1255 unsat1255 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c184 := h 183 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1256 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨12, by decide⟩, true), (⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1242, some c1082, some c76, some c114, some c69, some c53, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1256 : lratChecker f1256 p1256 = .success := by decide +kernel
theorem unsat1256 : Unsatisfiable (PosFin 31) f1256 := by
  apply lratCheckerSound f1256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1256
  · intro a ha; simp [p1256] at ha; subst a; trivial
  · exact checked1256
theorem derived1256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1256 := by
  apply localUnsat_implies_entails f1256 [c1184, c1254, c1242, c1082, c76, c114, c69, c53] c1256 unsat1256 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1242 := derived1242 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1257 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1184, some c26, some c64, some c78, some c72, some c366, some c1082, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1257 : lratChecker f1257 p1257 = .success := by decide +kernel
theorem unsat1257 : Unsatisfiable (PosFin 31) f1257 := by
  apply lratCheckerSound f1257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1257
  · intro a ha; simp [p1257] at ha; subst a; trivial
  · exact checked1257
theorem derived1257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1257 := by
  apply localUnsat_implies_entails f1257 [c1254, c1184, c26, c64, c78, c72, c366, c1082] c1257 unsat1257 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c366 := h 365 (by decide)
  have h7 : Entails.eval a c1082 := derived1082 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1258 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1257, some c201, some c1255, some c183, some c229, some c84, some c68, some c136, some c1256, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1258 : lratChecker f1258 p1258 = .success := by decide +kernel
theorem unsat1258 : Unsatisfiable (PosFin 31) f1258 := by
  apply lratCheckerSound f1258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1258
  · intro a ha; simp [p1258] at ha; subst a; trivial
  · exact checked1258
theorem derived1258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1258 := by
  apply localUnsat_implies_entails f1258 [c1184, c1254, c1257, c201, c1255, c183, c229, c84, c68, c136, c1256] c1258 unsat1258 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1257 := derived1257 a h
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c1255 := derived1255 a h
  have h5 : Entails.eval a c183 := h 182 (by decide)
  have h6 : Entails.eval a c229 := h 228 (by decide)
  have h7 : Entails.eval a c84 := h 83 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c1256 := derived1256 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1259 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1074, some c1120, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1259 : lratChecker f1259 p1259 = .success := by decide +kernel
theorem unsat1259 : Unsatisfiable (PosFin 31) f1259 := by
  apply lratCheckerSound f1259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1259
  · intro a ha; simp [p1259] at ha; subst a; trivial
  · exact checked1259
theorem derived1259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1259 := by
  apply localUnsat_implies_entails f1259 [c1184, c1074, c1120] c1259 unsat1259 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1074 := derived1074 a h
  have h2 : Entails.eval a c1120 := derived1120 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1260 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c269, some c274, some c298, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1260 : lratChecker f1260 p1260 = .success := by decide +kernel
theorem unsat1260 : Unsatisfiable (PosFin 31) f1260 := by
  apply lratCheckerSound f1260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1260
  · intro a ha; simp [p1260] at ha; subst a; trivial
  · exact checked1260
theorem derived1260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1260 := by
  apply localUnsat_implies_entails f1260 [c269, c274, c298] c1260 unsat1260 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c274 := h 273 (by decide)
  have h2 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1261 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨26, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1258, some c28, some c1260, some c1259, some c68, some c86, some c1106, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p1261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1261 : lratChecker f1261 p1261 = .success := by decide +kernel
theorem unsat1261 : Unsatisfiable (PosFin 31) f1261 := by
  apply lratCheckerSound f1261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1261
  · intro a ha; simp [p1261] at ha; subst a; trivial
  · exact checked1261
theorem derived1261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1261 := by
  apply localUnsat_implies_entails f1261 [c1184, c1254, c1258, c28, c1260, c1259, c68, c86, c1106] c1261 unsat1261 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1258 := derived1258 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c1260 := derived1260 a h
  have h5 : Entails.eval a c1259 := derived1259 a h
  have h6 : Entails.eval a c68 := h 67 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c1106 := derived1106 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1262 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1261, some c11, some c28, some c1260, some c565, some c584, some c21, some c1120, some c64, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1262 : lratChecker f1262 p1262 = .success := by decide +kernel
theorem unsat1262 : Unsatisfiable (PosFin 31) f1262 := by
  apply lratCheckerSound f1262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1262
  · intro a ha; simp [p1262] at ha; subst a; trivial
  · exact checked1262
theorem derived1262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1262 := by
  apply localUnsat_implies_entails f1262 [c1184, c1254, c1261, c11, c28, c1260, c565, c584, c21, c1120, c64] c1262 unsat1262 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1261 := derived1261 a h
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c1260 := derived1260 a h
  have h6 : Entails.eval a c565 := h 564 (by decide)
  have h7 : Entails.eval a c584 := h 583 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c1120 := derived1120 a h
  have h10 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1263 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1050, some c240, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1263 : lratChecker f1263 p1263 = .success := by decide +kernel
theorem unsat1263 : Unsatisfiable (PosFin 31) f1263 := by
  apply lratCheckerSound f1263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1263
  · intro a ha; simp [p1263] at ha; subst a; trivial
  · exact checked1263
theorem derived1263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1263 := by
  apply localUnsat_implies_entails f1263 [c1050, c240] c1263 unsat1263 (by rfl) a
  have h0 : Entails.eval a c1050 := derived1050 a h
  have h1 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1264 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1261, some c1262, some c18, some c1263, some c13, some c201, some c26, some c64, some c78, some c1242, some c641, some c529, some c736, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1264 : lratChecker f1264 p1264 = .success := by decide +kernel
theorem unsat1264 : Unsatisfiable (PosFin 31) f1264 := by
  apply lratCheckerSound f1264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1264
  · intro a ha; simp [p1264] at ha; subst a; trivial
  · exact checked1264
theorem derived1264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1264 := by
  apply localUnsat_implies_entails f1264 [c1184, c1254, c1261, c1262, c18, c1263, c13, c201, c26, c64, c78, c1242, c641, c529, c736] c1264 unsat1264 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1261 := derived1261 a h
  have h3 : Entails.eval a c1262 := derived1262 a h
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c1263 := derived1263 a h
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c1242 := derived1242 a h
  have h12 : Entails.eval a c641 := h 640 (by decide)
  have h13 : Entails.eval a c529 := h 528 (by decide)
  have h14 : Entails.eval a c736 := h 735 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1265 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1184, some c1264, some c1056, some c1037, some c1198, some c64, some c78, some c133, some c88, some c1036, some c469, some c1131, some c206, some c593, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1265 : lratChecker f1265 p1265 = .success := by decide +kernel
theorem unsat1265 : Unsatisfiable (PosFin 31) f1265 := by
  apply lratCheckerSound f1265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1265
  · intro a ha; simp [p1265] at ha; subst a; trivial
  · exact checked1265
theorem derived1265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1265 := by
  apply localUnsat_implies_entails f1265 [c1254, c1184, c1264, c1056, c1037, c1198, c64, c78, c133, c88, c1036, c469, c1131, c206, c593] c1265 unsat1265 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1264 := derived1264 a h
  have h3 : Entails.eval a c1056 := derived1056 a h
  have h4 : Entails.eval a c1037 := derived1037 a h
  have h5 : Entails.eval a c1198 := derived1198 a h
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c88 := h 87 (by decide)
  have h10 : Entails.eval a c1036 := derived1036 a h
  have h11 : Entails.eval a c469 := h 468 (by decide)
  have h12 : Entails.eval a c1131 := derived1131 a h
  have h13 : Entails.eval a c206 := h 205 (by decide)
  have h14 : Entails.eval a c593 := h 592 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1266 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1184, some c1265, some c1037, some c1198, some c64, some c78, some c133, some c88, some c1060, some c297, some c1122, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1266 : lratChecker f1266 p1266 = .success := by decide +kernel
theorem unsat1266 : Unsatisfiable (PosFin 31) f1266 := by
  apply lratCheckerSound f1266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1266
  · intro a ha; simp [p1266] at ha; subst a; trivial
  · exact checked1266
theorem derived1266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1266 := by
  apply localUnsat_implies_entails f1266 [c1254, c1184, c1265, c1037, c1198, c64, c78, c133, c88, c1060, c297, c1122] c1266 unsat1266 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1265 := derived1265 a h
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1198 := derived1198 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c1060 := derived1060 a h
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c1122 := derived1122 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1267 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1266, some c1265, some c78, some c1060, some c1244, some c204, some c281, some c114, some c252, some c1082, some c310, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1267 : lratChecker f1267 p1267 = .success := by decide +kernel
theorem unsat1267 : Unsatisfiable (PosFin 31) f1267 := by
  apply lratCheckerSound f1267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1267
  · intro a ha; simp [p1267] at ha; subst a; trivial
  · exact checked1267
theorem derived1267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1267 := by
  apply localUnsat_implies_entails f1267 [c1184, c1254, c1266, c1265, c78, c1060, c1244, c204, c281, c114, c252, c1082, c310] c1267 unsat1267 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1266 := derived1266 a h
  have h3 : Entails.eval a c1265 := derived1265 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c1060 := derived1060 a h
  have h6 : Entails.eval a c1244 := derived1244 a h
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c281 := h 280 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c252 := h 251 (by decide)
  have h11 : Entails.eval a c1082 := derived1082 a h
  have h12 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1268 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1267, some c1266, some c1265, some c1060, some c1244, some c281, some c252, some c18, some c55, some c1088, some c76, some c1052, some c1124, some c512, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1268 : lratChecker f1268 p1268 = .success := by decide +kernel
theorem unsat1268 : Unsatisfiable (PosFin 31) f1268 := by
  apply lratCheckerSound f1268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1268
  · intro a ha; simp [p1268] at ha; subst a; trivial
  · exact checked1268
theorem derived1268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1268 := by
  apply localUnsat_implies_entails f1268 [c1184, c1267, c1266, c1265, c1060, c1244, c281, c252, c18, c55, c1088, c76, c1052, c1124, c512] c1268 unsat1268 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1267 := derived1267 a h
  have h2 : Entails.eval a c1266 := derived1266 a h
  have h3 : Entails.eval a c1265 := derived1265 a h
  have h4 : Entails.eval a c1060 := derived1060 a h
  have h5 : Entails.eval a c1244 := derived1244 a h
  have h6 : Entails.eval a c281 := h 280 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c1088 := derived1088 a h
  have h11 : Entails.eval a c76 := h 75 (by decide)
  have h12 : Entails.eval a c1052 := derived1052 a h
  have h13 : Entails.eval a c1124 := derived1124 a h
  have h14 : Entails.eval a c512 := h 511 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1269 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨14, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1268, some c1267, some c1265, some c114, some c71, some c1046, some c1044, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1269 : lratChecker f1269 p1269 = .success := by decide +kernel
theorem unsat1269 : Unsatisfiable (PosFin 31) f1269 := by
  apply lratCheckerSound f1269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1269
  · intro a ha; simp [p1269] at ha; subst a; trivial
  · exact checked1269
theorem derived1269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1269 := by
  apply localUnsat_implies_entails f1269 [c1254, c1268, c1267, c1265, c114, c71, c1046, c1044] c1269 unsat1269 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1268 := derived1268 a h
  have h2 : Entails.eval a c1267 := derived1267 a h
  have h3 : Entails.eval a c1265 := derived1265 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c1046 := derived1046 a h
  have h7 : Entails.eval a c1044 := derived1044 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1270 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1266, some c1265, some c1267, some c1268, some c1269, some c55, some c1263, some c1044, some c369, some c1076, some c1040, some c134, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1270 : lratChecker f1270 p1270 = .success := by decide +kernel
theorem unsat1270 : Unsatisfiable (PosFin 31) f1270 := by
  apply lratCheckerSound f1270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1270
  · intro a ha; simp [p1270] at ha; subst a; trivial
  · exact checked1270
theorem derived1270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1270 := by
  apply localUnsat_implies_entails f1270 [c1184, c1266, c1265, c1267, c1268, c1269, c55, c1263, c1044, c369, c1076, c1040, c134] c1270 unsat1270 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1266 := derived1266 a h
  have h2 : Entails.eval a c1265 := derived1265 a h
  have h3 : Entails.eval a c1267 := derived1267 a h
  have h4 : Entails.eval a c1268 := derived1268 a h
  have h5 : Entails.eval a c1269 := derived1269 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c1263 := derived1263 a h
  have h8 : Entails.eval a c1044 := derived1044 a h
  have h9 : Entails.eval a c369 := h 368 (by decide)
  have h10 : Entails.eval a c1076 := derived1076 a h
  have h11 : Entails.eval a c1040 := derived1040 a h
  have h12 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1271 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1184, some c1270, some c64, some c68, some c1266, some c1265, some c57, some c1263, some c53, some c513, some c638, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1271 : lratChecker f1271 p1271 = .success := by decide +kernel
theorem unsat1271 : Unsatisfiable (PosFin 31) f1271 := by
  apply lratCheckerSound f1271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1271
  · intro a ha; simp [p1271] at ha; subst a; trivial
  · exact checked1271
theorem derived1271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1271 := by
  apply localUnsat_implies_entails f1271 [c1254, c1184, c1270, c64, c68, c1266, c1265, c57, c1263, c53, c513, c638] c1271 unsat1271 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1270 := derived1270 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c1266 := derived1266 a h
  have h6 : Entails.eval a c1265 := derived1265 a h
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c1263 := derived1263 a h
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c513 := h 512 (by decide)
  have h11 : Entails.eval a c638 := h 637 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1272 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1184, some c1265, some c1270, some c68, some c1271, some c86, some c106, some c860, some c1039, some c33, some c329, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p1272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1272 : lratChecker f1272 p1272 = .success := by decide +kernel
theorem unsat1272 : Unsatisfiable (PosFin 31) f1272 := by
  apply lratCheckerSound f1272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1272
  · intro a ha; simp [p1272] at ha; subst a; trivial
  · exact checked1272
theorem derived1272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1272 := by
  apply localUnsat_implies_entails f1272 [c1254, c1184, c1265, c1270, c68, c1271, c86, c106, c860, c1039, c33, c329] c1272 unsat1272 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1265 := derived1265 a h
  have h3 : Entails.eval a c1270 := derived1270 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c1271 := derived1271 a h
  have h6 : Entails.eval a c86 := h 85 (by decide)
  have h7 : Entails.eval a c106 := h 105 (by decide)
  have h8 : Entails.eval a c860 := derived860 a h
  have h9 : Entails.eval a c1039 := derived1039 a h
  have h10 : Entails.eval a c33 := h 32 (by decide)
  have h11 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1273 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1273 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1184, some c1254, some c68, some c1061, some c1037, some c1057, some c28, some c281, some c1064, some c1066, some c270, some c296, some c266, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1273 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1273 : lratChecker f1273 p1273 = .success := by decide +kernel
theorem unsat1273 : Unsatisfiable (PosFin 31) f1273 := by
  apply lratCheckerSound f1273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1273
  · intro a ha; simp [p1273] at ha; subst a; trivial
  · exact checked1273
theorem derived1273 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1273 := by
  apply localUnsat_implies_entails f1273 [c1272, c1184, c1254, c68, c1061, c1037, c1057, c28, c281, c1064, c1066, c270, c296, c266] c1273 unsat1273 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c68 := h 67 (by decide)
  have h4 : Entails.eval a c1061 := derived1061 a h
  have h5 : Entails.eval a c1037 := derived1037 a h
  have h6 : Entails.eval a c1057 := derived1057 a h
  have h7 : Entails.eval a c28 := h 27 (by decide)
  have h8 : Entails.eval a c281 := h 280 (by decide)
  have h9 : Entails.eval a c1064 := derived1064 a h
  have h10 : Entails.eval a c1066 := derived1066 a h
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c296 := h 295 (by decide)
  have h13 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1274 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1272, some c1184, some c1273, some c68, some c1061, some c28, some c281, some c1069, some c252, some c1068, some c750, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1274 : lratChecker f1274 p1274 = .success := by decide +kernel
theorem unsat1274 : Unsatisfiable (PosFin 31) f1274 := by
  apply lratCheckerSound f1274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1274
  · intro a ha; simp [p1274] at ha; subst a; trivial
  · exact checked1274
theorem derived1274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1274 := by
  apply localUnsat_implies_entails f1274 [c1254, c1272, c1184, c1273, c68, c1061, c28, c281, c1069, c252, c1068, c750] c1274 unsat1274 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1273 := derived1273 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c1061 := derived1061 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c1069 := derived1069 a h
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c1068 := derived1068 a h
  have h11 : Entails.eval a c750 := derived750 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1275 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1272, some c1273, some c1274, some c1035, some c206, some c179, some c186, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1275 : lratChecker f1275 p1275 = .success := by decide +kernel
theorem unsat1275 : Unsatisfiable (PosFin 31) f1275 := by
  apply lratCheckerSound f1275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1275
  · intro a ha; simp [p1275] at ha; subst a; trivial
  · exact checked1275
theorem derived1275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1275 := by
  apply localUnsat_implies_entails f1275 [c1254, c1272, c1273, c1274, c1035, c206, c179, c186] c1275 unsat1275 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1273 := derived1273 a h
  have h3 : Entails.eval a c1274 := derived1274 a h
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c179 := h 178 (by decide)
  have h7 : Entails.eval a c186 := h 185 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1276 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1184, some c1254, some c1275, some c1035, some c206, some c1036, some c65, some c80, some c750, some c1061, some c132, some c88, some c646, some c1090, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1276 : lratChecker f1276 p1276 = .success := by decide +kernel
theorem unsat1276 : Unsatisfiable (PosFin 31) f1276 := by
  apply lratCheckerSound f1276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1276
  · intro a ha; simp [p1276] at ha; subst a; trivial
  · exact checked1276
theorem derived1276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1276 := by
  apply localUnsat_implies_entails f1276 [c1272, c1184, c1254, c1275, c1035, c206, c1036, c65, c80, c750, c1061, c132, c88, c646, c1090] c1276 unsat1276 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c1036 := derived1036 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c750 := derived750 a h
  have h10 : Entails.eval a c1061 := derived1061 a h
  have h11 : Entails.eval a c132 := h 131 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c646 := h 645 (by decide)
  have h14 : Entails.eval a c1090 := derived1090 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1277 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1272, some c1184, some c1276, some c1275, some c65, some c202, some c1061, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1277 : lratChecker f1277 p1277 = .success := by decide +kernel
theorem unsat1277 : Unsatisfiable (PosFin 31) f1277 := by
  apply lratCheckerSound f1277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1277
  · intro a ha; simp [p1277] at ha; subst a; trivial
  · exact checked1277
theorem derived1277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1277 := by
  apply localUnsat_implies_entails f1277 [c1254, c1272, c1184, c1276, c1275, c65, c202, c1061] c1277 unsat1277 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1276 := derived1276 a h
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c1061 := derived1061 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1278 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1275, some c1276, some c1277, some c1060, some c28, some c281, some c252, some c55, some c1088, some c589, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1278 : lratChecker f1278 p1278 = .success := by decide +kernel
theorem unsat1278 : Unsatisfiable (PosFin 31) f1278 := by
  apply lratCheckerSound f1278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1278
  · intro a ha; simp [p1278] at ha; subst a; trivial
  · exact checked1278
theorem derived1278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1278 := by
  apply localUnsat_implies_entails f1278 [c1184, c1254, c1275, c1276, c1277, c1060, c28, c281, c252, c55, c1088, c589] c1278 unsat1278 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1275 := derived1275 a h
  have h3 : Entails.eval a c1276 := derived1276 a h
  have h4 : Entails.eval a c1277 := derived1277 a h
  have h5 : Entails.eval a c1060 := derived1060 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c1088 := derived1088 a h
  have h11 : Entails.eval a c589 := h 588 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1279 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1279 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1272, some c1278, some c1037, some c1275, some c1060, some c28, some c281, some c252, some c18, some c55, some c1088, some c76, some c875, some c1052, some c1124, some c1129, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1279 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1279 : lratChecker f1279 p1279 = .success := by decide +kernel
theorem unsat1279 : Unsatisfiable (PosFin 31) f1279 := by
  apply lratCheckerSound f1279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1279
  · intro a ha; simp [p1279] at ha; subst a; trivial
  · exact checked1279
theorem derived1279 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1279 := by
  apply localUnsat_implies_entails f1279 [c1184, c1272, c1278, c1037, c1275, c1060, c28, c281, c252, c18, c55, c1088, c76, c875, c1052, c1124, c1129] c1279 unsat1279 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1278 := derived1278 a h
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c1060 := derived1060 a h
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c55 := h 54 (by decide)
  have h11 : Entails.eval a c1088 := derived1088 a h
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c875 := derived875 a h
  have h14 : Entails.eval a c1052 := derived1052 a h
  have h15 : Entails.eval a c1124 := derived1124 a h
  have h16 : Entails.eval a c1129 := derived1129 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1280 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1280 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1279, some c1278, some c1037, some c1275, some c28, some c281, some c252, some c18, some c55, some c76, some c87, some c57, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1280 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1280 : lratChecker f1280 p1280 = .success := by decide +kernel
theorem unsat1280 : Unsatisfiable (PosFin 31) f1280 := by
  apply lratCheckerSound f1280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1280
  · intro a ha; simp [p1280] at ha; subst a; trivial
  · exact checked1280
theorem derived1280 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1280 := by
  apply localUnsat_implies_entails f1280 [c1184, c1279, c1278, c1037, c1275, c28, c281, c252, c18, c55, c76, c87, c57] c1280 unsat1280 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1279 := derived1279 a h
  have h2 : Entails.eval a c1278 := derived1278 a h
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1275 := derived1275 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c281 := h 280 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c18 := h 17 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c87 := h 86 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1281 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1281 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1272, some c1184, some c1275, some c1278, some c1280, some c1061, some c185, some c265, some c649, some c1112, some c636, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p1281 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1281 : lratChecker f1281 p1281 = .success := by decide +kernel
theorem unsat1281 : Unsatisfiable (PosFin 31) f1281 := by
  apply lratCheckerSound f1281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1281
  · intro a ha; simp [p1281] at ha; subst a; trivial
  · exact checked1281
theorem derived1281 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1281 := by
  apply localUnsat_implies_entails f1281 [c1254, c1272, c1184, c1275, c1278, c1280, c1061, c185, c265, c649, c1112, c636] c1281 unsat1281 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c1280 := derived1280 a h
  have h6 : Entails.eval a c1061 := derived1061 a h
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c265 := h 264 (by decide)
  have h9 : Entails.eval a c649 := h 648 (by decide)
  have h10 : Entails.eval a c1112 := derived1112 a h
  have h11 : Entails.eval a c636 := h 635 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1282 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1282 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1184, some c1281, some c1263, some c518, some c13, some c241, some c1126, some c1038, some c1259, some c1106, some c277, some c403, some c715, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1282 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1282 : lratChecker f1282 p1282 = .success := by decide +kernel
theorem unsat1282 : Unsatisfiable (PosFin 31) f1282 := by
  apply lratCheckerSound f1282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1282
  · intro a ha; simp [p1282] at ha; subst a; trivial
  · exact checked1282
theorem derived1282 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1282 := by
  apply localUnsat_implies_entails f1282 [c1272, c1184, c1281, c1263, c518, c13, c241, c1126, c1038, c1259, c1106, c277, c403, c715] c1282 unsat1282 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1281 := derived1281 a h
  have h3 : Entails.eval a c1263 := derived1263 a h
  have h4 : Entails.eval a c518 := h 517 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c241 := h 240 (by decide)
  have h7 : Entails.eval a c1126 := derived1126 a h
  have h8 : Entails.eval a c1038 := derived1038 a h
  have h9 : Entails.eval a c1259 := derived1259 a h
  have h10 : Entails.eval a c1106 := derived1106 a h
  have h11 : Entails.eval a c277 := h 276 (by decide)
  have h12 : Entails.eval a c403 := h 402 (by decide)
  have h13 : Entails.eval a c715 := h 714 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1283 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1283 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1281, some c1272, some c1184, some c1043, some c73, some c76, some c1053, some c635, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1283 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1283 : lratChecker f1283 p1283 = .success := by decide +kernel
theorem unsat1283 : Unsatisfiable (PosFin 31) f1283 := by
  apply lratCheckerSound f1283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1283
  · intro a ha; simp [p1283] at ha; subst a; trivial
  · exact checked1283
theorem derived1283 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1283 := by
  apply localUnsat_implies_entails f1283 [c1281, c1272, c1184, c1043, c73, c76, c1053, c635] c1283 unsat1283 (by rfl) a
  have h0 : Entails.eval a c1281 := derived1281 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1043 := derived1043 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c76 := h 75 (by decide)
  have h6 : Entails.eval a c1053 := derived1053 a h
  have h7 : Entails.eval a c635 := h 634 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1284 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1284 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1082, some c80, some c339, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1284 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1284 : lratChecker f1284 p1284 = .success := by decide +kernel
theorem unsat1284 : Unsatisfiable (PosFin 31) f1284 := by
  apply lratCheckerSound f1284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1284
  · intro a ha; simp [p1284] at ha; subst a; trivial
  · exact checked1284
theorem derived1284 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1284 := by
  apply localUnsat_implies_entails f1284 [c1184, c1082, c80, c339] c1284 unsat1284 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1285 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1285 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1272, some c18, some c1283, some c16, some c1284, some c87, some c237, some c1089, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1285 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1285 : lratChecker f1285 p1285 = .success := by decide +kernel
theorem unsat1285 : Unsatisfiable (PosFin 31) f1285 := by
  apply lratCheckerSound f1285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1285
  · intro a ha; simp [p1285] at ha; subst a; trivial
  · exact checked1285
theorem derived1285 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1285 := by
  apply localUnsat_implies_entails f1285 [c1184, c1272, c18, c1283, c16, c1284, c87, c237, c1089] c1285 unsat1285 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c1283 := derived1283 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1284 := derived1284 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c237 := h 236 (by decide)
  have h8 : Entails.eval a c1089 := derived1089 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1286 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1286 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1272, some c1184, some c1281, some c1282, some c1285, some c11, some c1260, some c364, some c32, some c1106, some c395, some c265, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1286 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1286 : lratChecker f1286 p1286 = .success := by decide +kernel
theorem unsat1286 : Unsatisfiable (PosFin 31) f1286 := by
  apply lratCheckerSound f1286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1286
  · intro a ha; simp [p1286] at ha; subst a; trivial
  · exact checked1286
theorem derived1286 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1286 := by
  apply localUnsat_implies_entails f1286 [c1254, c1272, c1184, c1281, c1282, c1285, c11, c1260, c364, c32, c1106, c395, c265] c1286 unsat1286 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1281 := derived1281 a h
  have h4 : Entails.eval a c1282 := derived1282 a h
  have h5 : Entails.eval a c1285 := derived1285 a h
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c1260 := derived1260 a h
  have h8 : Entails.eval a c364 := h 363 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c1106 := derived1106 a h
  have h11 : Entails.eval a c395 := h 394 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1287 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1287 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1281, some c1184, some c11, some c1260, some c278, some c32, some c1259, some c244, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1287 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1287 : lratChecker f1287 p1287 = .success := by decide +kernel
theorem unsat1287 : Unsatisfiable (PosFin 31) f1287 := by
  apply lratCheckerSound f1287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1287
  · intro a ha; simp [p1287] at ha; subst a; trivial
  · exact checked1287
theorem derived1287 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1287 := by
  apply localUnsat_implies_entails f1287 [c1281, c1184, c11, c1260, c278, c32, c1259, c244] c1287 unsat1287 (by rfl) a
  have h0 : Entails.eval a c1281 := derived1281 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c11 := h 10 (by decide)
  have h3 : Entails.eval a c1260 := derived1260 a h
  have h4 : Entails.eval a c278 := h 277 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c1259 := derived1259 a h
  have h7 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1288 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1288 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1281, some c1184, some c1038, some c1120, some c132, some c637, some c337, some c575, some c1209, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1288 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1288 : lratChecker f1288 p1288 = .success := by decide +kernel
theorem unsat1288 : Unsatisfiable (PosFin 31) f1288 := by
  apply lratCheckerSound f1288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1288
  · intro a ha; simp [p1288] at ha; subst a; trivial
  · exact checked1288
theorem derived1288 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1288 := by
  apply localUnsat_implies_entails f1288 [c1272, c1281, c1184, c1038, c1120, c132, c637, c337, c575, c1209] c1288 unsat1288 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1281 := derived1281 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1038 := derived1038 a h
  have h4 : Entails.eval a c1120 := derived1120 a h
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c637 := h 636 (by decide)
  have h7 : Entails.eval a c337 := h 336 (by decide)
  have h8 : Entails.eval a c575 := h 574 (by decide)
  have h9 : Entails.eval a c1209 := derived1209 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1289 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨27, by decide⟩, false), (⟨14, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1254, some c1272, some c1281, some c1286, some c1287, some c1288, some c269, some c1069, some c185, some c65, some c265, some c26, some c1077, some c648, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1289 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 31) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c1184, c1254, c1272, c1281, c1286, c1287, c1288, c269, c1069, c185, c65, c265, c26, c1077, c648] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1272 := derived1272 a h
  have h3 : Entails.eval a c1281 := derived1281 a h
  have h4 : Entails.eval a c1286 := derived1286 a h
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c1288 := derived1288 a h
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c1069 := derived1069 a h
  have h9 : Entails.eval a c185 := h 184 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c1077 := derived1077 a h
  have h14 : Entails.eval a c648 := h 647 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1281, some c1184, some c1254, some c1289, some c201, some c28, some c203, some c26, some c1069, some c80, some c132, some c269, some c1110, some c626, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1290 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 31) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c1272, c1281, c1184, c1254, c1289, c201, c28, c203, c26, c1069, c80, c132, c269, c1110, c626] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1281 := derived1281 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c1289 := derived1289 a h
  have h5 : Entails.eval a c201 := h 200 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c203 := h 202 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1069 := derived1069 a h
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c132 := h 131 (by decide)
  have h12 : Entails.eval a c269 := h 268 (by decide)
  have h13 : Entails.eval a c1110 := derived1110 a h
  have h14 : Entails.eval a c626 := h 625 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1291 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨27, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1281, some c1184, some c1272, some c1254, some c201, some c28, some c26, some c22, some c24, some c206, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1291 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 31) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c1281, c1184, c1272, c1254, c201, c28, c26, c22, c24, c206] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c1281 := derived1281 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1272 := derived1272 a h
  have h3 : Entails.eval a c1254 := derived1254 a h
  have h4 : Entails.eval a c201 := h 200 (by decide)
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1254, some c22, some c24, some c206, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1292 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 31) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c1272, c1254, c22, c24, c206] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1293 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1281, some c1184, some c1254, some c1272, some c1292, some c1291, some c206, some c20, some c62, some c183, some c1069, some c84, some c265, some c136, some c1038, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1293 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 31) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c1281, c1184, c1254, c1272, c1292, c1291, c206, c20, c62, c183, c1069, c84, c265, c136, c1038] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c1281 := derived1281 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c1292 := derived1292 a h
  have h5 : Entails.eval a c1291 := derived1291 a h
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c62 := h 61 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c1069 := derived1069 a h
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c265 := h 264 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c1038 := derived1038 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1294 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1294 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1272, some c1281, some c1184, some c1290, some c1292, some c1293, some c185, some c1069, some c67, some c62, some c228, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1294 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1294 : lratChecker f1294 p1294 = .success := by decide +kernel
theorem unsat1294 : Unsatisfiable (PosFin 31) f1294 := by
  apply lratCheckerSound f1294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1294
  · intro a ha; simp [p1294] at ha; subst a; trivial
  · exact checked1294
theorem derived1294 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1294 := by
  apply localUnsat_implies_entails f1294 [c1254, c1272, c1281, c1184, c1290, c1292, c1293, c185, c1069, c67, c62, c228] c1294 unsat1294 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1272 := derived1272 a h
  have h2 : Entails.eval a c1281 := derived1281 a h
  have h3 : Entails.eval a c1184 := derived1184 a h
  have h4 : Entails.eval a c1290 := derived1290 a h
  have h5 : Entails.eval a c1292 := derived1292 a h
  have h6 : Entails.eval a c1293 := derived1293 a h
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c1069 := derived1069 a h
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1295 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1295 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1184, some c1281, some c1290, some c1291, some c1260, some c1038, some c1120, some c1085, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1295 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1295 : lratChecker f1295 p1295 = .success := by decide +kernel
theorem unsat1295 : Unsatisfiable (PosFin 31) f1295 := by
  apply lratCheckerSound f1295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1295
  · intro a ha; simp [p1295] at ha; subst a; trivial
  · exact checked1295
theorem derived1295 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1295 := by
  apply localUnsat_implies_entails f1295 [c1272, c1184, c1281, c1290, c1291, c1260, c1038, c1120, c1085] c1295 unsat1295 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1281 := derived1281 a h
  have h3 : Entails.eval a c1290 := derived1290 a h
  have h4 : Entails.eval a c1291 := derived1291 a h
  have h5 : Entails.eval a c1260 := derived1260 a h
  have h6 : Entails.eval a c1038 := derived1038 a h
  have h7 : Entails.eval a c1120 := derived1120 a h
  have h8 : Entails.eval a c1085 := derived1085 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1296 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1296 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1281, some c1184, some c1272, some c1290, some c1291, some c1295, some c1294, some c21, some c26, some c62, some c183, some c84, some c1069, some c89, some c136, some c1098, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1296 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1296 : lratChecker f1296 p1296 = .success := by decide +kernel
theorem unsat1296 : Unsatisfiable (PosFin 31) f1296 := by
  apply lratCheckerSound f1296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1296
  · intro a ha; simp [p1296] at ha; subst a; trivial
  · exact checked1296
theorem derived1296 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1296 := by
  apply localUnsat_implies_entails f1296 [c1254, c1281, c1184, c1272, c1290, c1291, c1295, c1294, c21, c26, c62, c183, c84, c1069, c89, c136, c1098] c1296 unsat1296 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1281 := derived1281 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c1290 := derived1290 a h
  have h5 : Entails.eval a c1291 := derived1291 a h
  have h6 : Entails.eval a c1295 := derived1295 a h
  have h7 : Entails.eval a c1294 := derived1294 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c62 := h 61 (by decide)
  have h11 : Entails.eval a c183 := h 182 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c1069 := derived1069 a h
  have h14 : Entails.eval a c89 := h 88 (by decide)
  have h15 : Entails.eval a c136 := h 135 (by decide)
  have h16 : Entails.eval a c1098 := derived1098 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1297 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1297 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1281, some c1184, some c1254, some c1272, some c1296, some c1056, some c1037, some c1035, some c206, some c1036, some c65, some c80, some c1069, some c88, some c1130, some c1083, some c1090, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1297 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1297 : lratChecker f1297 p1297 = .success := by decide +kernel
theorem unsat1297 : Unsatisfiable (PosFin 31) f1297 := by
  apply lratCheckerSound f1297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1297
  · intro a ha; simp [p1297] at ha; subst a; trivial
  · exact checked1297
theorem derived1297 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1297 := by
  apply localUnsat_implies_entails f1297 [c1281, c1184, c1254, c1272, c1296, c1056, c1037, c1035, c206, c1036, c65, c80, c1069, c88, c1130, c1083, c1090] c1297 unsat1297 (by rfl) a
  have h0 : Entails.eval a c1281 := derived1281 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1254 := derived1254 a h
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c1296 := derived1296 a h
  have h5 : Entails.eval a c1056 := derived1056 a h
  have h6 : Entails.eval a c1037 := derived1037 a h
  have h7 : Entails.eval a c1035 := derived1035 a h
  have h8 : Entails.eval a c206 := h 205 (by decide)
  have h9 : Entails.eval a c1036 := derived1036 a h
  have h10 : Entails.eval a c65 := h 64 (by decide)
  have h11 : Entails.eval a c80 := h 79 (by decide)
  have h12 : Entails.eval a c1069 := derived1069 a h
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c1130 := derived1130 a h
  have h15 : Entails.eval a c1083 := derived1083 a h
  have h16 : Entails.eval a c1090 := derived1090 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1298 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1298 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1297, some c1254, some c68, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1298 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1298 : lratChecker f1298 p1298 = .success := by decide +kernel
theorem unsat1298 : Unsatisfiable (PosFin 31) f1298 := by
  apply lratCheckerSound f1298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1298
  · intro a ha; simp [p1298] at ha; subst a; trivial
  · exact checked1298
theorem derived1298 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1298 := by
  apply localUnsat_implies_entails f1298 [c1297, c1254, c68] c1298 unsat1298 (by rfl) a
  have h0 : Entails.eval a c1297 := derived1297 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1299 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨6, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1281, some c1298, some c1184, some c28, some c1260, some c1106, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1299 : lratChecker f1299 p1299 = .success := by decide +kernel
theorem unsat1299 : Unsatisfiable (PosFin 31) f1299 := by
  apply lratCheckerSound f1299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1299
  · intro a ha; simp [p1299] at ha; subst a; trivial
  · exact checked1299
theorem derived1299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1299 := by
  apply localUnsat_implies_entails f1299 [c1281, c1298, c1184, c28, c1260, c1106] c1299 unsat1299 (by rfl) a
  have h0 : Entails.eval a c1281 := derived1281 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c1260 := derived1260 a h
  have h5 : Entails.eval a c1106 := derived1106 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1300 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1300 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1272, some c1184, some c1298, some c1281, some c1035, some c1299, some c1069, some c1091, some c269, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1300 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1300 : lratChecker f1300 p1300 = .success := by decide +kernel
theorem unsat1300 : Unsatisfiable (PosFin 31) f1300 := by
  apply lratCheckerSound f1300 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1300
  · intro a ha; simp [p1300] at ha; subst a; trivial
  · exact checked1300
theorem derived1300 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1300 := by
  apply localUnsat_implies_entails f1300 [c1272, c1184, c1298, c1281, c1035, c1299, c1069, c1091, c269] c1300 unsat1300 (by rfl) a
  have h0 : Entails.eval a c1272 := derived1272 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1298 := derived1298 a h
  have h3 : Entails.eval a c1281 := derived1281 a h
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c1299 := derived1299 a h
  have h6 : Entails.eval a c1069 := derived1069 a h
  have h7 : Entails.eval a c1091 := derived1091 a h
  have h8 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1301 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1301 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1254, some c1298, some c1272, some c1184, some c1297, some c1281, some c106, some c1300, some c179, some c1037, some c1299, some c1069, some c1066, some c1062, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1301 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1301 : lratChecker f1301 p1301 = .success := by decide +kernel
theorem unsat1301 : Unsatisfiable (PosFin 31) f1301 := by
  apply lratCheckerSound f1301 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1301
  · intro a ha; simp [p1301] at ha; subst a; trivial
  · exact checked1301
theorem derived1301 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1301 := by
  apply localUnsat_implies_entails f1301 [c1254, c1298, c1272, c1184, c1297, c1281, c106, c1300, c179, c1037, c1299, c1069, c1066, c1062] c1301 unsat1301 (by rfl) a
  have h0 : Entails.eval a c1254 := derived1254 a h
  have h1 : Entails.eval a c1298 := derived1298 a h
  have h2 : Entails.eval a c1272 := derived1272 a h
  have h3 : Entails.eval a c1184 := derived1184 a h
  have h4 : Entails.eval a c1297 := derived1297 a h
  have h5 : Entails.eval a c1281 := derived1281 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c1300 := derived1300 a h
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c1037 := derived1037 a h
  have h10 : Entails.eval a c1299 := derived1299 a h
  have h11 : Entails.eval a c1069 := derived1069 a h
  have h12 : Entails.eval a c1066 := derived1066 a h
  have h13 : Entails.eval a c1062 := derived1062 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1302 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1302 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1301, some c1254, some c1297, some c860, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1302 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1302 : lratChecker f1302 p1302 = .success := by decide +kernel
theorem unsat1302 : Unsatisfiable (PosFin 31) f1302 := by
  apply lratCheckerSound f1302 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1302
  · intro a ha; simp [p1302] at ha; subst a; trivial
  · exact checked1302
theorem derived1302 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1302 := by
  apply localUnsat_implies_entails f1302 [c1301, c1254, c1297, c860] c1302 unsat1302 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1254 := derived1254 a h
  have h2 : Entails.eval a c1297 := derived1297 a h
  have h3 : Entails.eval a c860 := derived860 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1303 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1303 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1302, some c1301, some c1039, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1303 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1303 : lratChecker f1303 p1303 = .success := by decide +kernel
theorem unsat1303 : Unsatisfiable (PosFin 31) f1303 := by
  apply lratCheckerSound f1303 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1303
  · intro a ha; simp [p1303] at ha; subst a; trivial
  · exact checked1303
theorem derived1303 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1303 := by
  apply localUnsat_implies_entails f1303 [c1302, c1301, c1039] c1303 unsat1303 (by rfl) a
  have h0 : Entails.eval a c1302 := derived1302 a h
  have h1 : Entails.eval a c1301 := derived1301 a h
  have h2 : Entails.eval a c1039 := derived1039 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1304 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1304 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1301, some c1297, some c1298, some c1272, some c1184, some c1068, some c1069, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1304 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1304 : lratChecker f1304 p1304 = .success := by decide +kernel
theorem unsat1304 : Unsatisfiable (PosFin 31) f1304 := by
  apply lratCheckerSound f1304 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1304
  · intro a ha; simp [p1304] at ha; subst a; trivial
  · exact checked1304
theorem derived1304 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1304 := by
  apply localUnsat_implies_entails f1304 [c1301, c1297, c1298, c1272, c1184, c1068, c1069] c1304 unsat1304 (by rfl) a
  have h0 : Entails.eval a c1301 := derived1301 a h
  have h1 : Entails.eval a c1297 := derived1297 a h
  have h2 : Entails.eval a c1298 := derived1298 a h
  have h3 : Entails.eval a c1272 := derived1272 a h
  have h4 : Entails.eval a c1184 := derived1184 a h
  have h5 : Entails.eval a c1068 := derived1068 a h
  have h6 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1305 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1305 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1304, some c1303, some c1281, some c1260, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1305 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1305 : lratChecker f1305 p1305 = .success := by decide +kernel
theorem unsat1305 : Unsatisfiable (PosFin 31) f1305 := by
  apply lratCheckerSound f1305 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1305
  · intro a ha; simp [p1305] at ha; subst a; trivial
  · exact checked1305
theorem derived1305 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1305 := by
  apply localUnsat_implies_entails f1305 [c1304, c1303, c1281, c1260] c1305 unsat1305 (by rfl) a
  have h0 : Entails.eval a c1304 := derived1304 a h
  have h1 : Entails.eval a c1303 := derived1303 a h
  have h2 : Entails.eval a c1281 := derived1281 a h
  have h3 : Entails.eval a c1260 := derived1260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1306 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1306 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1304, some c1281, some c1303, some c274, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1306 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1306 : lratChecker f1306 p1306 = .success := by decide +kernel
theorem unsat1306 : Unsatisfiable (PosFin 31) f1306 := by
  apply lratCheckerSound f1306 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1306
  · intro a ha; simp [p1306] at ha; subst a; trivial
  · exact checked1306
theorem derived1306 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1306 := by
  apply localUnsat_implies_entails f1306 [c1304, c1281, c1303, c274] c1306 unsat1306 (by rfl) a
  have h0 : Entails.eval a c1304 := derived1304 a h
  have h1 : Entails.eval a c1281 := derived1281 a h
  have h2 : Entails.eval a c1303 := derived1303 a h
  have h3 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1307 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1307 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1305, some c1281, some c1056, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1307 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1307 : lratChecker f1307 p1307 = .success := by decide +kernel
theorem unsat1307 : Unsatisfiable (PosFin 31) f1307 := by
  apply lratCheckerSound f1307 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1307
  · intro a ha; simp [p1307] at ha; subst a; trivial
  · exact checked1307
theorem derived1307 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1307 := by
  apply localUnsat_implies_entails f1307 [c1305, c1281, c1056] c1307 unsat1307 (by rfl) a
  have h0 : Entails.eval a c1305 := derived1305 a h
  have h1 : Entails.eval a c1281 := derived1281 a h
  have h2 : Entails.eval a c1056 := derived1056 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1308 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1308 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1305, some c1184, some c1037, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p1308 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1308 : lratChecker f1308 p1308 = .success := by decide +kernel
theorem unsat1308 : Unsatisfiable (PosFin 31) f1308 := by
  apply lratCheckerSound f1308 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1308
  · intro a ha; simp [p1308] at ha; subst a; trivial
  · exact checked1308
theorem derived1308 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1308 := by
  apply localUnsat_implies_entails f1308 [c1305, c1184, c1037] c1308 unsat1308 (by rfl) a
  have h0 : Entails.eval a c1305 := derived1305 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1037 := derived1037 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1309 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1309 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1306, some c1184, some c1307, some c1301, some c1101, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1309 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1309 : lratChecker f1309 p1309 = .success := by decide +kernel
theorem unsat1309 : Unsatisfiable (PosFin 31) f1309 := by
  apply lratCheckerSound f1309 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1309
  · intro a ha; simp [p1309] at ha; subst a; trivial
  · exact checked1309
theorem derived1309 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1309 := by
  apply localUnsat_implies_entails f1309 [c1306, c1184, c1307, c1301, c1101] c1309 unsat1309 (by rfl) a
  have h0 : Entails.eval a c1306 := derived1306 a h
  have h1 : Entails.eval a c1184 := derived1184 a h
  have h2 : Entails.eval a c1307 := derived1307 a h
  have h3 : Entails.eval a c1301 := derived1301 a h
  have h4 : Entails.eval a c1101 := derived1101 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1310 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f1310 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1306, some c1308, some c1302, some c1304, some c1309, some c1281, some c491]
def p1310 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1310 : lratChecker f1310 p1310 = .success := by decide +kernel
theorem unsat1310 : Unsatisfiable (PosFin 31) f1310 := by
  apply lratCheckerSound f1310 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1310
  · intro a ha; simp [p1310] at ha; subst a; trivial
  · exact checked1310
theorem derived1310 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1310 := by
  apply localUnsat_implies_entails f1310 [c1306, c1308, c1302, c1304, c1309, c1281, c491] c1310 unsat1310 (by rfl) a
  have h0 : Entails.eval a c1306 := derived1306 a h
  have h1 : Entails.eval a c1308 := derived1308 a h
  have h2 : Entails.eval a c1302 := derived1302 a h
  have h3 : Entails.eval a c1304 := derived1304 a h
  have h4 : Entails.eval a c1309 := derived1309 a h
  have h5 : Entails.eval a c1281 := derived1281 a h
  have h6 : Entails.eval a c491 := h 490 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1310

end CochromaticTwenty.Certificates.Z12Direct_5_8_7
