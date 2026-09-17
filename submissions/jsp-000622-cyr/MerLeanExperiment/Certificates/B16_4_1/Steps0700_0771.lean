import MerLeanExperiment.Certificates.B16_4_1.Steps0600_0699

/-! Generated from the actual pinned b16_4_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1085 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1078, some c1084, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 57) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c1078, c1084] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c1078 := derived1078 a h
  have h1 : Entails.eval a c1084 := derived1084 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1086 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c100, some c102, some c56, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 57) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c100, c102, c56] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c100 := h 99 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c255, some c253, some c32, some c56, some c95, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p1087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 57) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1058, c255, c253, c32, c56, c95] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c255 := h 254 (by decide)
  have h2 : Entails.eval a c253 := h 252 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c303, some c301, some c255, some c253, some c1085, some c346, some c351, some c198, some c204, some c37, some c108, some c1087, some c7, some c128, some c144, some c190, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 57) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c1058, c303, c301, c255, c253, c1085, c346, c351, c198, c204, c37, c108, c1087, c7, c128, c144, c190] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c303 := h 302 (by decide)
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c1085 := derived1085 a h
  have h6 : Entails.eval a c346 := h 345 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c204 := h 203 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c1087 := derived1087 a h
  have h13 : Entails.eval a c7 := h 6 (by decide)
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c144 := h 143 (by decide)
  have h16 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1089 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c828, some c1085, some c346, some c301, some c303, some c1086, some c1088, some c64, some c57, some c50, some c101, some c96, some c341, some c94, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1089 : lratChecker f1089 p1089 = .success := by decide +kernel
theorem unsat1089 : Unsatisfiable (PosFin 57) f1089 := by
  apply lratCheckerSound f1089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1089
  · intro a ha; simp [p1089] at ha; subst a; trivial
  · exact checked1089
theorem derived1089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1089 := by
  apply localUnsat_implies_entails f1089 [c1032, c828, c1085, c346, c301, c303, c1086, c1088, c64, c57, c50, c101, c96, c341, c94] c1089 unsat1089 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c303 := h 302 (by decide)
  have h6 : Entails.eval a c1086 := derived1086 a h
  have h7 : Entails.eval a c1088 := derived1088 a h
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c50 := h 49 (by decide)
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c341 := h 340 (by decide)
  have h14 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1090 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1058, some c1085, some c346, some c253, some c1089, some c264, some c41, some c198, some c100, some c102, some c57, some c30, some c196, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1090 : lratChecker f1090 p1090 = .success := by decide +kernel
theorem unsat1090 : Unsatisfiable (PosFin 57) f1090 := by
  apply lratCheckerSound f1090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1090
  · intro a ha; simp [p1090] at ha; subst a; trivial
  · exact checked1090
theorem derived1090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1090 := by
  apply localUnsat_implies_entails f1090 [c1032, c1058, c1085, c346, c253, c1089, c264, c41, c198, c100, c102, c57, c30, c196] c1090 unsat1090 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c1089 := derived1089 a h
  have h6 : Entails.eval a c264 := h 263 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c57 := h 56 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1091 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1058, some c264, some c41, some c100, some c31, some c196, some c1086, some c57, some c298, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1091 : lratChecker f1091 p1091 = .success := by decide +kernel
theorem unsat1091 : Unsatisfiable (PosFin 57) f1091 := by
  apply lratCheckerSound f1091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1091
  · intro a ha; simp [p1091] at ha; subst a; trivial
  · exact checked1091
theorem derived1091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1091 := by
  apply localUnsat_implies_entails f1091 [c1032, c1058, c264, c41, c100, c31, c196, c1086, c57, c298] c1091 unsat1091 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  have h7 : Entails.eval a c1086 := derived1086 a h
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1092 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, false), (⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c31, some c56, some c252, some c98, some c35, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1092 : lratChecker f1092 p1092 = .success := by decide +kernel
theorem unsat1092 : Unsatisfiable (PosFin 57) f1092 := by
  apply lratCheckerSound f1092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1092
  · intro a ha; simp [p1092] at ha; subst a; trivial
  · exact checked1092
theorem derived1092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1092 := by
  apply localUnsat_implies_entails f1092 [c1058, c31, c56, c252, c98, c35] c1092 unsat1092 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c56 := h 55 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1093 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c828, some c1085, some c346, some c1090, some c1091, some c301, some c303, some c1086, some c64, some c1092, some c101, some c96, some c94, some c93, some c341, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1093 : lratChecker f1093 p1093 = .success := by decide +kernel
theorem unsat1093 : Unsatisfiable (PosFin 57) f1093 := by
  apply lratCheckerSound f1093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1093
  · intro a ha; simp [p1093] at ha; subst a; trivial
  · exact checked1093
theorem derived1093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1093 := by
  apply localUnsat_implies_entails f1093 [c1032, c828, c1085, c346, c1090, c1091, c301, c303, c1086, c64, c1092, c101, c96, c94, c93, c341] c1093 unsat1093 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c1090 := derived1090 a h
  have h5 : Entails.eval a c1091 := derived1091 a h
  have h6 : Entails.eval a c301 := h 300 (by decide)
  have h7 : Entails.eval a c303 := h 302 (by decide)
  have h8 : Entails.eval a c1086 := derived1086 a h
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c1092 := derived1092 a h
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c96 := h 95 (by decide)
  have h13 : Entails.eval a c94 := h 93 (by decide)
  have h14 : Entails.eval a c93 := h 92 (by decide)
  have h15 : Entails.eval a c341 := h 340 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1094 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c828, some c1058, some c100, some c64, some c96, some c52, some c35, some c866, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1094 : lratChecker f1094 p1094 = .success := by decide +kernel
theorem unsat1094 : Unsatisfiable (PosFin 57) f1094 := by
  apply lratCheckerSound f1094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1094
  · intro a ha; simp [p1094] at ha; subst a; trivial
  · exact checked1094
theorem derived1094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1094 := by
  apply localUnsat_implies_entails f1094 [c1032, c828, c1058, c100, c64, c96, c52, c35, c866] c1094 unsat1094 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1058 := derived1058 a h
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c64 := h 63 (by decide)
  have h5 : Entails.eval a c96 := h 95 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c866 := derived866 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1095 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨27, by decide⟩, true), (⟨25, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1094, some c57, some c298, some c1086, some c1092, some c64, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1095 : lratChecker f1095 p1095 = .success := by decide +kernel
theorem unsat1095 : Unsatisfiable (PosFin 57) f1095 := by
  apply lratCheckerSound f1095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1095
  · intro a ha; simp [p1095] at ha; subst a; trivial
  · exact checked1095
theorem derived1095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1095 := by
  apply localUnsat_implies_entails f1095 [c1032, c1094, c57, c298, c1086, c1092, c64] c1095 unsat1095 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1094 := derived1094 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c1086 := derived1086 a h
  have h5 : Entails.eval a c1092 := derived1092 a h
  have h6 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1096 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c828, some c1032, some c1085, some c346, some c351, some c1093, some c263, some c1095, some c253, some c255, some c198, some c50, some c57, some c341, some c101, some c100, some c94, some c32, some c64, some c98, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1096 : lratChecker f1096 p1096 = .success := by decide +kernel
theorem unsat1096 : Unsatisfiable (PosFin 57) f1096 := by
  apply lratCheckerSound f1096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1096
  · intro a ha; simp [p1096] at ha; subst a; trivial
  · exact checked1096
theorem derived1096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1096 := by
  apply localUnsat_implies_entails f1096 [c1058, c828, c1032, c1085, c346, c351, c1093, c263, c1095, c253, c255, c198, c50, c57, c341, c101, c100, c94, c32, c64, c98] c1096 unsat1096 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c1085 := derived1085 a h
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  have h6 : Entails.eval a c1093 := derived1093 a h
  have h7 : Entails.eval a c263 := h 262 (by decide)
  have h8 : Entails.eval a c1095 := derived1095 a h
  have h9 : Entails.eval a c253 := h 252 (by decide)
  have h10 : Entails.eval a c255 := h 254 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c341 := h 340 (by decide)
  have h15 : Entails.eval a c101 := h 100 (by decide)
  have h16 : Entails.eval a c100 := h 99 (by decide)
  have h17 : Entails.eval a c94 := h 93 (by decide)
  have h18 : Entails.eval a c32 := h 31 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  have h20 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1097 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨6, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c828, some c1058, some c1085, some c346, some c351, some c1093, some c263, some c1096, some c296, some c297, some c288, some c295, some c341, some c379, some c50, some c89, some c198, some c1094, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 57) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c828, c1058, c1085, c346, c351, c1093, c263, c1096, c296, c297, c288, c295, c341, c379, c50, c89, c198, c1094] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c828 := derived828 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c1093 := derived1093 a h
  have h6 : Entails.eval a c263 := h 262 (by decide)
  have h7 : Entails.eval a c1096 := derived1096 a h
  have h8 : Entails.eval a c296 := h 295 (by decide)
  have h9 : Entails.eval a c297 := h 296 (by decide)
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c295 := h 294 (by decide)
  have h12 : Entails.eval a c341 := h 340 (by decide)
  have h13 : Entails.eval a c379 := h 378 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c89 := h 88 (by decide)
  have h16 : Entails.eval a c198 := h 197 (by decide)
  have h17 : Entails.eval a c1094 := derived1094 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c828, some c1058, some c52, some c35, some c866, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 57) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c828, c1058, c52, c35, c866] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c828 := derived828 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c866 := derived866 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1099 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨1, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, true), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1098, some c96, some c31, some c201, some c57, some c1092, some c304, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1099 : lratChecker f1099 p1099 = .success := by decide +kernel
theorem unsat1099 : Unsatisfiable (PosFin 57) f1099 := by
  apply lratCheckerSound f1099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1099
  · intro a ha; simp [p1099] at ha; subst a; trivial
  · exact checked1099
theorem derived1099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1099 := by
  apply localUnsat_implies_entails f1099 [c1098, c96, c31, c201, c57, c1092, c304] c1099 unsat1099 (by rfl) a
  have h0 : Entails.eval a c1098 := derived1098 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c201 := h 200 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c1092 := derived1092 a h
  have h6 : Entails.eval a c304 := h 303 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1100 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c828, some c1085, some c346, some c351, some c1097, some c20, some c38, some c63, some c1099, some c253, some c204, some c50, some c242, some c87, some c96, some c98, some c57, some c30, some c201, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1100 : lratChecker f1100 p1100 = .success := by decide +kernel
theorem unsat1100 : Unsatisfiable (PosFin 57) f1100 := by
  apply lratCheckerSound f1100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1100
  · intro a ha; simp [p1100] at ha; subst a; trivial
  · exact checked1100
theorem derived1100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1100 := by
  apply localUnsat_implies_entails f1100 [c1058, c828, c1085, c346, c351, c1097, c20, c38, c63, c1099, c253, c204, c50, c242, c87, c96, c98, c57, c30, c201] c1100 unsat1100 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c1097 := derived1097 a h
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c1099 := derived1099 a h
  have h10 : Entails.eval a c253 := h 252 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c242 := h 241 (by decide)
  have h14 : Entails.eval a c87 := h 86 (by decide)
  have h15 : Entails.eval a c96 := h 95 (by decide)
  have h16 : Entails.eval a c98 := h 97 (by decide)
  have h17 : Entails.eval a c57 := h 56 (by decide)
  have h18 : Entails.eval a c30 := h 29 (by decide)
  have h19 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1101 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1100, some c1085, some c346, some c351, some c253, some c255, some c1079, some c63, some c99, some c97, some c32, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1101 : lratChecker f1101 p1101 = .success := by decide +kernel
theorem unsat1101 : Unsatisfiable (PosFin 57) f1101 := by
  apply lratCheckerSound f1101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1101
  · intro a ha; simp [p1101] at ha; subst a; trivial
  · exact checked1101
theorem derived1101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1101 := by
  apply localUnsat_implies_entails f1101 [c1058, c1100, c1085, c346, c351, c253, c255, c1079, c63, c99, c97, c32] c1101 unsat1101 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c351 := h 350 (by decide)
  have h5 : Entails.eval a c253 := h 252 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c1079 := derived1079 a h
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1102 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true), (⟨1, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨33, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c828, some c32, some c251, some c205, some c865, some c30, some c58, some c133, some c96, some c299, some c52, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false))]
def p1102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1102 : lratChecker f1102 p1102 = .success := by decide +kernel
theorem unsat1102 : Unsatisfiable (PosFin 57) f1102 := by
  apply lratCheckerSound f1102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1102
  · intro a ha; simp [p1102] at ha; subst a; trivial
  · exact checked1102
theorem derived1102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1102 := by
  apply localUnsat_implies_entails f1102 [c1058, c828, c32, c251, c205, c865, c30, c58, c133, c96, c299, c52] c1102 unsat1102 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c865 := derived865 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c299 := h 298 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1103 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c828, some c1100, some c1085, some c346, some c351, some c20, some c38, some c63, some c99, some c97, some c1102, some c258, some c202, some c23, some c48, some c58, some c240, some c302, some c87, some c791, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 57) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c1032, c828, c1100, c1085, c346, c351, c20, c38, c63, c99, c97, c1102, c258, c202, c23, c48, c58, c240, c302, c87, c791] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1085 := derived1085 a h
  have h4 : Entails.eval a c346 := h 345 (by decide)
  have h5 : Entails.eval a c351 := h 350 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c1102 := derived1102 a h
  have h12 : Entails.eval a c258 := h 257 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c23 := h 22 (by decide)
  have h15 : Entails.eval a c48 := h 47 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c240 := h 239 (by decide)
  have h18 : Entails.eval a c302 := h 301 (by decide)
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c791 := derived791 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨26, by decide⟩, false), (⟨3, by decide⟩, true), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1100, some c1103, some c104, some c103, some c58, some c56, some c302, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 57) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c1100, c1103, c104, c103, c58, c56, c302] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c1100 := derived1100 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c104 := h 103 (by decide)
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c58 := h 57 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c302 := h 301 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, true), (⟨20, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1032, some c1085, some c346, some c1104, some c303, some c197, some c264, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 57) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c1058, c1032, c1085, c346, c1104, c303, c197, c264] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c346 := h 345 (by decide)
  have h4 : Entails.eval a c1104 := derived1104 a h
  have h5 : Entails.eval a c303 := h 302 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨20, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1100, some c1103, some c104, some c103, some c1085, some c346, some c351, some c1105, some c263, some c197, some c58, some c56, some c296, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 57) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c1058, c1100, c1103, c104, c103, c1085, c346, c351, c1105, c263, c197, c58, c56, c296] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c1085 := derived1085 a h
  have h6 : Entails.eval a c346 := h 345 (by decide)
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c1105 := derived1105 a h
  have h9 : Entails.eval a c263 := h 262 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c56 := h 55 (by decide)
  have h13 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨1, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1058, some c1100, some c1103, some c104, some c1101, some c1085, some c351, some c254, some c1106, some c100, some c96, some c23, some c36, some c258, some c251, some c108, some c9, some c6, some c127, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 57) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c1032, c1058, c1100, c1103, c104, c1101, c1085, c351, c254, c1106, c100, c96, c23, c36, c258, c251, c108, c9, c6, c127] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1103 := derived1103 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c1101 := derived1101 a h
  have h6 : Entails.eval a c1085 := derived1085 a h
  have h7 : Entails.eval a c351 := h 350 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c1106 := derived1106 a h
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c96 := h 95 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c258 := h 257 (by decide)
  have h15 : Entails.eval a c251 := h 250 (by decide)
  have h16 : Entails.eval a c108 := h 107 (by decide)
  have h17 : Entails.eval a c9 := h 8 (by decide)
  have h18 : Entails.eval a c6 := h 5 (by decide)
  have h19 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1100, some c1103, some c104, some c103, some c1101, some c1085, some c346, some c351, some c1107, some c32, some c251, some c865, some c30, some c151, some c9, some c6, some c127, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 57) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c1058, c1100, c1103, c104, c103, c1101, c1085, c346, c351, c1107, c32, c251, c865, c30, c151, c9, c6, c127] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c1101 := derived1101 a h
  have h6 : Entails.eval a c1085 := derived1085 a h
  have h7 : Entails.eval a c346 := h 345 (by decide)
  have h8 : Entails.eval a c351 := h 350 (by decide)
  have h9 : Entails.eval a c1107 := derived1107 a h
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c865 := derived865 a h
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c6 := h 5 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1109 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1032, some c346, some c1100, some c1103, some c103, some c104, some c1108, some c64, some c100, some c1106, some c32, some c30, some c251, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 57) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c1058, c1032, c346, c1100, c1103, c103, c104, c1108, c64, c100, c1106, c32, c30, c251] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c346 := h 345 (by decide)
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c1103 := derived1103 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c104 := h 103 (by decide)
  have h7 : Entails.eval a c1108 := derived1108 a h
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c1106 := derived1106 a h
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c30 := h 29 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1110 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1085, some c1109, some (DefaultClause.unit (⟨39, by decide⟩, true))]
def p1110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 57) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c1085, c1109] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c1085 := derived1085 a h
  have h1 : Entails.eval a c1109 := derived1109 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1111 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c1058, some c971, some c25, some c43, some c251, some c199, some c21, some c37, some c343, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 57) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c1110, c1058, c971, c25, c43, c251, c199, c21, c37, c343] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c43 := h 42 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1058, some c1110, some c1032, some c828, some c1111, some c255, some c251, some c31, some c30, some c21, some c104, some c343, some c63, some c37, some c64, some c199, some c106, some c270, some c87, some c675, some c329, some c47, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 57) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c971, c1058, c1110, c1032, c828, c1111, c255, c251, c31, c30, c21, c104, c343, c63, c37, c64, c199, c106, c270, c87, c675, c329, c47] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1110 := derived1110 a h
  have h3 : Entails.eval a c1032 := derived1032 a h
  have h4 : Entails.eval a c828 := derived828 a h
  have h5 : Entails.eval a c1111 := derived1111 a h
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c251 := h 250 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c343 := h 342 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c37 := h 36 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c106 := h 105 (by decide)
  have h18 : Entails.eval a c270 := h 269 (by decide)
  have h19 : Entails.eval a c87 := h 86 (by decide)
  have h20 : Entails.eval a c675 := derived675 a h
  have h21 : Entails.eval a c329 := h 328 (by decide)
  have h22 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c971, some c1032, some c828, some c1112, some c219, some c345, some c64, some c37, some c30, some c21, some c102, some c106, some c63, some c52, some c87, some c297, some c329, some c47, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 57) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c1110, c971, c1032, c828, c1112, c219, c345, c64, c37, c30, c21, c102, c106, c63, c52, c87, c297, c329, c47] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c1112 := derived1112 a h
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  have h16 : Entails.eval a c297 := h 296 (by decide)
  have h17 : Entails.eval a c329 := h 328 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1114 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨49, by decide⟩, true), (⟨35, by decide⟩, false), (⟨51, by decide⟩, false), (⟨33, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c63, some c85, some c329, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 57) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c63, c85, c329] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c63 := h 62 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  have h2 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c971, some c1032, some c1058, some c1111, some c1112, some c219, some c345, some c37, some c64, some c1113, some c196, some c47, some c39, some c234, some c1114, some c104, some c1086, some c57, some c298, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 57) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c1110, c971, c1032, c1058, c1111, c1112, c219, c345, c37, c64, c1113, c196, c47, c39, c234, c1114, c104, c1086, c57, c298] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1111 := derived1111 a h
  have h5 : Entails.eval a c1112 := derived1112 a h
  have h6 : Entails.eval a c219 := h 218 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c37 := h 36 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c1113 := derived1113 a h
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c234 := h 233 (by decide)
  have h15 : Entails.eval a c1114 := derived1114 a h
  have h16 : Entails.eval a c104 := h 103 (by decide)
  have h17 : Entails.eval a c1086 := derived1086 a h
  have h18 : Entails.eval a c57 := h 56 (by decide)
  have h19 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1110, some c971, some c1032, some c1115, some c252, some c251, some c221, some c219, some c25, some c256, some c345, some c101, some c64, some c29, some c105, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 57) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c1058, c1110, c971, c1032, c1115, c252, c251, c221, c219, c25, c256, c345, c101, c64, c29, c105] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1110 := derived1110 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c1032 := derived1032 a h
  have h4 : Entails.eval a c1115 := derived1115 a h
  have h5 : Entails.eval a c252 := h 251 (by decide)
  have h6 : Entails.eval a c251 := h 250 (by decide)
  have h7 : Entails.eval a c221 := h 220 (by decide)
  have h8 : Entails.eval a c219 := h 218 (by decide)
  have h9 : Entails.eval a c25 := h 24 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  have h11 : Entails.eval a c345 := h 344 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c64 := h 63 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨3, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c828, some c1058, some c1032, some c64, some c100, some c105, some c37, some c52, some c200, some c29, some c297, some c299, some c87, some c63, some c350, some c330, some c1063, some c289, some c329, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 57) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c828, c1058, c1032, c64, c100, c105, c37, c52, c200, c29, c297, c299, c87, c63, c350, c330, c1063, c289, c329] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c828 := derived828 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c299 := h 298 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c350 := h 349 (by decide)
  have h15 : Entails.eval a c330 := h 329 (by decide)
  have h16 : Entails.eval a c1063 := derived1063 a h
  have h17 : Entails.eval a c289 := h 288 (by decide)
  have h18 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨20, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c828, some c1110, some c1058, some c1115, some c37, some c64, some c105, some c52, some c299, some c1117, some c219, some c268, some c199, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 57) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c1032, c828, c1110, c1058, c1115, c37, c64, c105, c52, c299, c1117, c219, c268, c199] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c828 := derived828 a h
  have h2 : Entails.eval a c1110 := derived1110 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1115 := derived1115 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c299 := h 298 (by decide)
  have h10 : Entails.eval a c1117 := derived1117 a h
  have h11 : Entails.eval a c219 := h 218 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1116, some c1118, some c343, some c345, some c217, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 57) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c971, c1116, c1118, c343, c345, c217] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1116 := derived1116 a h
  have h2 : Entails.eval a c1118 := derived1118 a h
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c217 := h 216 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1110, some c1032, some c345, some c343, some c40, some c266, some c268, some c302, some c296, some c53, some c102, some c101, some c70, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 57) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c971, c1110, c1032, c345, c343, c40, c266, c268, c302, c296, c53, c102, c101, c70] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1110 := derived1110 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c345 := h 344 (by decide)
  have h4 : Entails.eval a c343 := h 342 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c302 := h 301 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c53 := h 52 (by decide)
  have h11 : Entails.eval a c102 := h 101 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨28, by decide⟩, false), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c41, some c23, some c209, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 57) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c1032, c41, c23, c209] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1032, some c343, some c1119, some c21, some c109, some c1120, some c1121, some c100, some c105, some c11, some c806, some c137, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 57) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c971, c1032, c343, c1119, c21, c109, c1120, c1121, c100, c105, c11, c806, c137] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c343 := h 342 (by decide)
  have h3 : Entails.eval a c1119 := derived1119 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c1120 := derived1120 a h
  have h7 : Entails.eval a c1121 := derived1121 a h
  have h8 : Entails.eval a c100 := h 99 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c806 := derived806 a h
  have h12 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨33, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1110, some c1032, some c1119, some c1122, some c251, some c221, some c258, some c25, some c254, some c1120, some c101, some c1121, some c29, some c105, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 57) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c1058, c1110, c1032, c1119, c1122, c251, c221, c258, c25, c254, c1120, c101, c1121, c29, c105] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1110 := derived1110 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c1119 := derived1119 a h
  have h4 : Entails.eval a c1122 := derived1122 a h
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c221 := h 220 (by decide)
  have h7 : Entails.eval a c258 := h 257 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c254 := h 253 (by decide)
  have h10 : Entails.eval a c1120 := derived1120 a h
  have h11 : Entails.eval a c101 := h 100 (by decide)
  have h12 : Entails.eval a c1121 := derived1121 a h
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1058, some c1110, some c1032, some c1119, some c343, some c345, some c1122, some c251, some c221, some c258, some c1123, some c39, some c66, some c206, some c1071, some c41, some c102, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 57) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c971, c1058, c1110, c1032, c1119, c343, c345, c1122, c251, c221, c258, c1123, c39, c66, c206, c1071, c41, c102] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1110 := derived1110 a h
  have h3 : Entails.eval a c1032 := derived1032 a h
  have h4 : Entails.eval a c1119 := derived1119 a h
  have h5 : Entails.eval a c343 := h 342 (by decide)
  have h6 : Entails.eval a c345 := h 344 (by decide)
  have h7 : Entails.eval a c1122 := derived1122 a h
  have h8 : Entails.eval a c251 := h 250 (by decide)
  have h9 : Entails.eval a c221 := h 220 (by decide)
  have h10 : Entails.eval a c258 := h 257 (by decide)
  have h11 : Entails.eval a c1123 := derived1123 a h
  have h12 : Entails.eval a c39 := h 38 (by decide)
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c206 := h 205 (by decide)
  have h15 : Entails.eval a c1071 := derived1071 a h
  have h16 : Entails.eval a c41 := h 40 (by decide)
  have h17 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1058, some c1111, some c1119, some c1124, some c37, some c197, some c64, some c253, some c1086, some c104, some c196, some c31, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 57) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c1032, c1058, c1111, c1119, c1124, c37, c197, c64, c253, c1086, c104, c196, c31] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1111 := derived1111 a h
  have h3 : Entails.eval a c1119 := derived1119 a h
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c253 := h 252 (by decide)
  have h9 : Entails.eval a c1086 := derived1086 a h
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c196 := h 195 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1032, some c828, some c1110, some c1124, some c63, some c1119, some c37, some c197, some c296, some c297, some c270, some c52, some c301, some c629, some c46, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 57) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c1058, c1032, c828, c1110, c1124, c63, c1119, c37, c197, c296, c297, c270, c52, c301, c629, c46] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c1110 := derived1110 a h
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c1119 := derived1119 a h
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c296 := h 295 (by decide)
  have h10 : Entails.eval a c297 := h 296 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c52 := h 51 (by decide)
  have h13 : Entails.eval a c301 := h 300 (by decide)
  have h14 : Entails.eval a c629 := derived629 a h
  have h15 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1058, some c828, some c1119, some c1124, some c37, some c197, some c64, some c1125, some c63, some c1126, some c47, some c791, some c87, some c39, some c329, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 57) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c1032, c1058, c828, c1119, c1124, c37, c197, c64, c1125, c63, c1126, c47, c791, c87, c39, c329] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c1119 := derived1119 a h
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c1125 := derived1125 a h
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c1126 := derived1126 a h
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c791 := derived791 a h
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c329 := h 328 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1058, some c1032, some c1119, some c254, some c1124, some c37, some c64, some c197, some c1127, some c1117, some c100, some c105, some c40, some c136, some c29, some c14, some c258, some c111, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p1128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 57) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c1058, c1032, c1119, c254, c1124, c37, c64, c197, c1127, c1117, c100, c105, c40, c136, c29, c14, c258, c111] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c1058 := derived1058 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1119 := derived1119 a h
  have h3 : Entails.eval a c254 := h 253 (by decide)
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c37 := h 36 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c197 := h 196 (by decide)
  have h8 : Entails.eval a c1127 := derived1127 a h
  have h9 : Entails.eval a c1117 := derived1117 a h
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c136 := h 135 (by decide)
  have h14 : Entails.eval a c29 := h 28 (by decide)
  have h15 : Entails.eval a c14 := h 13 (by decide)
  have h16 : Entails.eval a c258 := h 257 (by decide)
  have h17 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c1032, some c828, some c1058, some c1128, some c971, some c95, some c96, some c25, some c70, some c94, some c52, some c100, some c87, some c243, some c382, some c29, some c93, some c254, some c866, some c97, some c345, some c22, some (DefaultClause.unit (⟨3, by decide⟩, true))]
def p1129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 57) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c1110, c1032, c828, c1058, c1128, c971, c95, c96, c25, c70, c94, c52, c100, c87, c243, c382, c29, c93, c254, c866, c97, c345, c22] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1128 := derived1128 a h
  have h5 : Entails.eval a c971 := derived971 a h
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  have h12 : Entails.eval a c100 := h 99 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c243 := h 242 (by decide)
  have h15 : Entails.eval a c382 := h 381 (by decide)
  have h16 : Entails.eval a c29 := h 28 (by decide)
  have h17 : Entails.eval a c93 := h 92 (by decide)
  have h18 : Entails.eval a c254 := h 253 (by decide)
  have h19 : Entails.eval a c866 := derived866 a h
  have h20 : Entails.eval a c97 := h 96 (by decide)
  have h21 : Entails.eval a c345 := h 344 (by decide)
  have h22 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1129, some c828, some c1058, some c1128, some c39, some c343, some c47, some c772, some c56, some c97, some c98, some c57, some c1092, some c52, some c204, some c866, some c29, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 57) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c971, c1129, c828, c1058, c1128, c39, c343, c47, c772, c56, c97, c98, c57, c1092, c52, c204, c866, c29] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1128 := derived1128 a h
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c772 := derived772 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c97 := h 96 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c1092 := derived1092 a h
  have h14 : Entails.eval a c52 := h 51 (by decide)
  have h15 : Entails.eval a c204 := h 203 (by decide)
  have h16 : Entails.eval a c866 := derived866 a h
  have h17 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1032, some c1129, some c1058, some c1128, some c1110, some c47, some c39, some c772, some c343, some c1130, some c303, some c304, some c264, some c270, some c57, some c199, some c99, some c25, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 57) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c971, c1032, c1129, c1058, c1128, c1110, c47, c39, c772, c343, c1130, c303, c304, c264, c270, c57, c199, c99, c25] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1129 := derived1129 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1128 := derived1128 a h
  have h5 : Entails.eval a c1110 := derived1110 a h
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c39 := h 38 (by decide)
  have h8 : Entails.eval a c772 := derived772 a h
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c1130 := derived1130 a h
  have h11 : Entails.eval a c303 := h 302 (by decide)
  have h12 : Entails.eval a c304 := h 303 (by decide)
  have h13 : Entails.eval a c264 := h 263 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c57 := h 56 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c99 := h 98 (by decide)
  have h18 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1110, some c301, some c302, some c270, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 57) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c1032, c1110, c301, c302, c270] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1110 := derived1110 a h
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c302 := h 301 (by decide)
  have h4 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨33, by decide⟩, true), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c1032, some c264, some c270, some c296, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 57) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c1110, c1032, c264, c270, c296] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c264 := h 263 (by decide)
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c1058, some c1032, some c1129, some c1128, some c1131, some c1132, some c38, some c675, some c98, some c811, some c221, some c255, some c251, some c220, some c31, some c1048, some c99, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 57) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c1110, c1058, c1032, c1129, c1128, c1131, c1132, c38, c675, c98, c811, c221, c255, c251, c220, c31, c1048, c99] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1032 := derived1032 a h
  have h3 : Entails.eval a c1129 := derived1129 a h
  have h4 : Entails.eval a c1128 := derived1128 a h
  have h5 : Entails.eval a c1131 := derived1131 a h
  have h6 : Entails.eval a c1132 := derived1132 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c675 := derived675 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c811 := derived811 a h
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c31 := h 30 (by decide)
  have h16 : Entails.eval a c1048 := derived1048 a h
  have h17 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c1129, some c1128, some c1058, some c1032, some c1110, some c343, some c345, some c21, some c840, some c252, some c251, some c29, some c221, some c219, some c258, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 57) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c971, c1129, c1128, c1058, c1032, c1110, c343, c345, c21, c840, c252, c251, c29, c221, c219, c258] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c1128 := derived1128 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1032 := derived1032 a h
  have h5 : Entails.eval a c1110 := derived1110 a h
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c840 := derived840 a h
  have h10 : Entails.eval a c252 := h 251 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c221 := h 220 (by decide)
  have h14 : Entails.eval a c219 := h 218 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1128, some c1131, some c1132, some c46, some c38, some c1135, some c1133, some c675, some c1134, some c98, some c630, some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 57) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c1128, c1131, c1132, c46, c38, c1135, c1133, c675, c1134, c98, c630] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c1128 := derived1128 a h
  have h1 : Entails.eval a c1131 := derived1131 a h
  have h2 : Entails.eval a c1132 := derived1132 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c1135 := derived1135 a h
  have h6 : Entails.eval a c1133 := derived1133 a h
  have h7 : Entails.eval a c675 := derived675 a h
  have h8 : Entails.eval a c1134 := derived1134 a h
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c630 := derived630 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c828, some c1032, some c1110, some c1129, some c1128, some c1136, some c306, some c52, some c98, some c1132, some c288, some c221, some c113, some c25, some c811, some c4, some c10, some c630, some c151, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 57) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c828, c1032, c1110, c1129, c1128, c1136, c306, c52, c98, c1132, c288, c221, c113, c25, c811, c4, c10, c630, c151] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c828 := derived828 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1110 := derived1110 a h
  have h3 : Entails.eval a c1129 := derived1129 a h
  have h4 : Entails.eval a c1128 := derived1128 a h
  have h5 : Entails.eval a c1136 := derived1136 a h
  have h6 : Entails.eval a c306 := h 305 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c1132 := derived1132 a h
  have h10 : Entails.eval a c288 := h 287 (by decide)
  have h11 : Entails.eval a c221 := h 220 (by decide)
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c811 := derived811 a h
  have h15 : Entails.eval a c4 := h 3 (by decide)
  have h16 : Entails.eval a c10 := h 9 (by decide)
  have h17 : Entails.eval a c630 := derived630 a h
  have h18 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c828, some c1129, some c1058, some c1110, some c1032, some c1128, some c1136, some c306, some c52, some c98, some c1132, some c1137, some c255, some c251, some c31, some c30, some c104, some c254, some c70, some c843, some c143, some c131, some c9, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 57) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c828, c1129, c1058, c1110, c1032, c1128, c1136, c306, c52, c98, c1132, c1137, c255, c251, c31, c30, c104, c254, c70, c843, c143, c131, c9] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c828 := derived828 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c1058 := derived1058 a h
  have h3 : Entails.eval a c1110 := derived1110 a h
  have h4 : Entails.eval a c1032 := derived1032 a h
  have h5 : Entails.eval a c1128 := derived1128 a h
  have h6 : Entails.eval a c1136 := derived1136 a h
  have h7 : Entails.eval a c306 := h 305 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c1132 := derived1132 a h
  have h11 : Entails.eval a c1137 := derived1137 a h
  have h12 : Entails.eval a c255 := h 254 (by decide)
  have h13 : Entails.eval a c251 := h 250 (by decide)
  have h14 : Entails.eval a c31 := h 30 (by decide)
  have h15 : Entails.eval a c30 := h 29 (by decide)
  have h16 : Entails.eval a c104 := h 103 (by decide)
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c70 := h 69 (by decide)
  have h19 : Entails.eval a c843 := derived843 a h
  have h20 : Entails.eval a c143 := h 142 (by decide)
  have h21 : Entails.eval a c131 := h 130 (by decide)
  have h22 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1128, some c971, some c828, some c306, some c52, some c1138, some c343, some c345, some c840, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 57) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c1128, c971, c828, c306, c52, c1138, c343, c345, c840] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c1128 := derived1128 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c828 := derived828 a h
  have h3 : Entails.eval a c306 := h 305 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c1138 := derived1138 a h
  have h6 : Entails.eval a c343 := h 342 (by decide)
  have h7 : Entails.eval a c345 := h 344 (by decide)
  have h8 : Entails.eval a c840 := derived840 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1032, some c1136, some c971, some c1129, some c1139, some c41, some c1133, some c102, some c343, some c345, some c66, some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 57) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c1032, c1136, c971, c1129, c1139, c41, c1133, c102, c343, c345, c66] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c1032 := derived1032 a h
  have h1 : Entails.eval a c1136 := derived1136 a h
  have h2 : Entails.eval a c971 := derived971 a h
  have h3 : Entails.eval a c1129 := derived1129 a h
  have h4 : Entails.eval a c1139 := derived1139 a h
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c1133 := derived1133 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c343 := h 342 (by decide)
  have h9 : Entails.eval a c345 := h 344 (by decide)
  have h10 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1140, some c1129, some c47, some (DefaultClause.unit (⟨51, by decide⟩, false))]
def p1141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 57) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c1140, c1129, c47] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1140, some c1129, some c39, some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 57) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c1140, c1129, c39] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1142, some c971, some c343, some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 57) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c1142, c971, c343] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c1142 := derived1142 a h
  have h1 : Entails.eval a c971 := derived971 a h
  have h2 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1110, some c1032, some c1143, some c1058, some c1140, some c1129, some c1136, some c41, some c270, some c264, some c1086, some c300, some c199, some c197, some c57, some c1066, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 57) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c1110, c1032, c1143, c1058, c1140, c1129, c1136, c41, c270, c264, c1086, c300, c199, c197, c57, c1066] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c1110 := derived1110 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1058 := derived1058 a h
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c1129 := derived1129 a h
  have h6 : Entails.eval a c1136 := derived1136 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c264 := h 263 (by decide)
  have h10 : Entails.eval a c1086 := derived1086 a h
  have h11 : Entails.eval a c300 := h 299 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c1066 := derived1066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1144, some c1142, some c1141, some c828, some c1143, some c1058, some c1140, some c1129, some c1136, some c303, some c307, some c288, some c379, some c329, some c295, some c263, some c300, some c199, some c197, some c57, some c1066, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p1145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 57) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1144, c1142, c1141, c828, c1143, c1058, c1140, c1129, c1136, c303, c307, c288, c379, c329, c295, c263, c300, c199, c197, c57, c1066] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1142 := derived1142 a h
  have h2 : Entails.eval a c1141 := derived1141 a h
  have h3 : Entails.eval a c828 := derived828 a h
  have h4 : Entails.eval a c1143 := derived1143 a h
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c1140 := derived1140 a h
  have h7 : Entails.eval a c1129 := derived1129 a h
  have h8 : Entails.eval a c1136 := derived1136 a h
  have h9 : Entails.eval a c303 := h 302 (by decide)
  have h10 : Entails.eval a c307 := h 306 (by decide)
  have h11 : Entails.eval a c288 := h 287 (by decide)
  have h12 : Entails.eval a c379 := h 378 (by decide)
  have h13 : Entails.eval a c329 := h 328 (by decide)
  have h14 : Entails.eval a c295 := h 294 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c300 := h 299 (by decide)
  have h17 : Entails.eval a c199 := h 198 (by decide)
  have h18 : Entails.eval a c197 := h 196 (by decide)
  have h19 : Entails.eval a c57 := h 56 (by decide)
  have h20 : Entails.eval a c1066 := derived1066 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1145, some c1140, some c1129, some c56, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 57) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1145, c1140, c1129, c56] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1145 := derived1145 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1129 := derived1129 a h
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1145, some c1140, some c1136, some c1086, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 57) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c1145, c1140, c1136, c1086] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c1145 := derived1145 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1136 := derived1136 a h
  have h3 : Entails.eval a c1086 := derived1086 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1146, some c1128, some c97, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 57) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c1146, c1128, c97] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c1146 := derived1146 a h
  have h1 : Entails.eval a c1128 := derived1128 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1032, some c1110, some c70, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 57) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c1147, c1032, c1110, c70] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1032 := derived1032 a h
  have h2 : Entails.eval a c1110 := derived1110 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 57 := directClause [(⟨30, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1148, some c1129, some c1140, some c57, some (DefaultClause.unit (⟨30, by decide⟩, false))]
def p1150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 57) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1148, c1129, c1140, c57] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1148, some c1128, some c1140, some c1145, some c1129, some c1092, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 57) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1148, c1128, c1140, c1145, c1129, c1092] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1128 := derived1128 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1145 := derived1145 a h
  have h4 : Entails.eval a c1129 := derived1129 a h
  have h5 : Entails.eval a c1092 := derived1092 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1151, some c1058, some c255, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 57) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c1151, c1058, c255] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c1151 := derived1151 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c255 := h 254 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 57 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1151, some c1058, some c1150, some c198, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p1153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 57) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1151, c1058, c1150, c198] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1151 := derived1151 a h
  have h1 : Entails.eval a c1058 := derived1058 a h
  have h2 : Entails.eval a c1150 := derived1150 a h
  have h3 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1152, some c1110, some c113, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p1154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 57) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c1152, c1110, c113] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c1110 := derived1110 a h
  have h2 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1153, some c1143, some c133, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p1155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 57) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1153, c1143, c133] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 57 := directClause [] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1154, some c1155, some c1128, some c1149, some c4]
def p1156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 57) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c1154, c1155, c1128, c1149, c4] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c1154 := derived1154 a h
  have h1 : Entails.eval a c1155 := derived1155 a h
  have h2 : Entails.eval a c1128 := derived1128 a h
  have h3 : Entails.eval a c1149 := derived1149 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1156

end CochromaticTwenty.Certificates.B16_4_1
