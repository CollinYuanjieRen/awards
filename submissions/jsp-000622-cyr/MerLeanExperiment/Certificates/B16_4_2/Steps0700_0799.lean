import MerLeanExperiment.Certificates.B16_4_2.Steps0600_0699

/-! Generated from the actual pinned b16_4_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_4_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1084 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1084 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c117, some c21, some c968, some c820, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1084 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1084 : lratChecker f1084 p1084 = .success := by decide +kernel
theorem unsat1084 : Unsatisfiable (PosFin 57) f1084 := by
  apply lratCheckerSound f1084 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1084
  · intro a ha; simp [p1084] at ha; subst a; trivial
  · exact checked1084
theorem derived1084 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1084 := by
  apply localUnsat_implies_entails f1084 [c272, c117, c21, c968, c820] c1084 unsat1084 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c968 := derived968 a h
  have h4 : Entails.eval a c820 := derived820 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1085 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1085 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c31, some c110, some c8, some c30, some c1001, some c269, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1085 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1085 : lratChecker f1085 p1085 = .success := by decide +kernel
theorem unsat1085 : Unsatisfiable (PosFin 57) f1085 := by
  apply lratCheckerSound f1085 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1085
  · intro a ha; simp [p1085] at ha; subst a; trivial
  · exact checked1085
theorem derived1085 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1085 := by
  apply localUnsat_implies_entails f1085 [c31, c110, c8, c30, c1001, c269] c1085 unsat1085 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c1001 := derived1001 a h
  have h5 : Entails.eval a c269 := h 268 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1086 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨31, by decide⟩, false), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1086 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c228, some c1085, some c270, some c267, some c224, some c906, some c631, some c26, some c513, some c354, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1086 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1086 : lratChecker f1086 p1086 = .success := by decide +kernel
theorem unsat1086 : Unsatisfiable (PosFin 57) f1086 := by
  apply lratCheckerSound f1086 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1086
  · intro a ha; simp [p1086] at ha; subst a; trivial
  · exact checked1086
theorem derived1086 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1086 := by
  apply localUnsat_implies_entails f1086 [c1077, c228, c1085, c270, c267, c224, c906, c631, c26, c513, c354] c1086 unsat1086 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c1085 := derived1085 a h
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c224 := h 223 (by decide)
  have h6 : Entails.eval a c906 := derived906 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c513 := derived513 a h
  have h10 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1087 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨19, by decide⟩, true), (⟨39, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1087 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c208, some c165, some c147, some c797, some c1086, some c265, some c631, some c26, some c1, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1087 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1087 : lratChecker f1087 p1087 = .success := by decide +kernel
theorem unsat1087 : Unsatisfiable (PosFin 57) f1087 := by
  apply lratCheckerSound f1087 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1087
  · intro a ha; simp [p1087] at ha; subst a; trivial
  · exact checked1087
theorem derived1087 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1087 := by
  apply localUnsat_implies_entails f1087 [c1077, c208, c165, c147, c797, c1086, c265, c631, c26, c1] c1087 unsat1087 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c797 := derived797 a h
  have h5 : Entails.eval a c1086 := derived1086 a h
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1088 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1088 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1083, some c1077, some c1084, some c1087, some c145, some c117, some c222, some c265, some c147, some c43, some c1080, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1088 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1088 : lratChecker f1088 p1088 = .success := by decide +kernel
theorem unsat1088 : Unsatisfiable (PosFin 57) f1088 := by
  apply lratCheckerSound f1088 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1088
  · intro a ha; simp [p1088] at ha; subst a; trivial
  · exact checked1088
theorem derived1088 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1088 := by
  apply localUnsat_implies_entails f1088 [c1083, c1077, c1084, c1087, c145, c117, c222, c265, c147, c43, c1080] c1088 unsat1088 (by rfl) a
  have h0 : Entails.eval a c1083 := derived1083 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1084 := derived1084 a h
  have h3 : Entails.eval a c1087 := derived1087 a h
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c222 := h 221 (by decide)
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c1080 := derived1080 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1089 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨9, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1089 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c208, some c203, some c171, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1089 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1089 : lratChecker f1089 p1089 = .success := by decide +kernel
theorem unsat1089 : Unsatisfiable (PosFin 57) f1089 := by
  apply lratCheckerSound f1089 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1089
  · intro a ha; simp [p1089] at ha; subst a; trivial
  · exact checked1089
theorem derived1089 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1089 := by
  apply localUnsat_implies_entails f1089 [c208, c203, c171] c1089 unsat1089 (by rfl) a
  have h0 : Entails.eval a c208 := h 207 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1090 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨35, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1090 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1089, some c513, some c1077, some c164, some c145, some c171, some c204, some c892, some c8, some c47, some c842, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1090 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1090 : lratChecker f1090 p1090 = .success := by decide +kernel
theorem unsat1090 : Unsatisfiable (PosFin 57) f1090 := by
  apply lratCheckerSound f1090 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1090
  · intro a ha; simp [p1090] at ha; subst a; trivial
  · exact checked1090
theorem derived1090 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1090 := by
  apply localUnsat_implies_entails f1090 [c1089, c513, c1077, c164, c145, c171, c204, c892, c8, c47, c842] c1090 unsat1090 (by rfl) a
  have h0 : Entails.eval a c1089 := derived1089 a h
  have h1 : Entails.eval a c513 := derived513 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c171 := h 170 (by decide)
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c892 := derived892 a h
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c842 := derived842 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1091 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨40, by decide⟩, true), (⟨39, by decide⟩, false), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1091 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c19, some c631, some c26, some c1089, some c1090, some c207, some c1, some c41, some c75, some c892, some c107, some c47, some c841, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1091 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1091 : lratChecker f1091 p1091 = .success := by decide +kernel
theorem unsat1091 : Unsatisfiable (PosFin 57) f1091 := by
  apply lratCheckerSound f1091 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1091
  · intro a ha; simp [p1091] at ha; subst a; trivial
  · exact checked1091
theorem derived1091 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1091 := by
  apply localUnsat_implies_entails f1091 [c1077, c19, c631, c26, c1089, c1090, c207, c1, c41, c75, c892, c107, c47, c841] c1091 unsat1091 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c1089 := derived1089 a h
  have h5 : Entails.eval a c1090 := derived1090 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c41 := h 40 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c892 := derived892 a h
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c841 := derived841 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1092 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1092 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c265, some c267, some c235, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1092 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1092 : lratChecker f1092 p1092 = .success := by decide +kernel
theorem unsat1092 : Unsatisfiable (PosFin 57) f1092 := by
  apply lratCheckerSound f1092 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1092
  · intro a ha; simp [p1092] at ha; subst a; trivial
  · exact checked1092
theorem derived1092 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1092 := by
  apply localUnsat_implies_entails f1092 [c265, c267, c235] c1092 unsat1092 (by rfl) a
  have h0 : Entails.eval a c265 := h 264 (by decide)
  have h1 : Entails.eval a c267 := h 266 (by decide)
  have h2 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1093 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨4, by decide⟩, true), (⟨34, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1093 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1083, some c1088, some c355, some c1092, some c1091, some c272, some c734, some c228, some c21, some c268, some c807, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1093 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1093 : lratChecker f1093 p1093 = .success := by decide +kernel
theorem unsat1093 : Unsatisfiable (PosFin 57) f1093 := by
  apply lratCheckerSound f1093 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1093
  · intro a ha; simp [p1093] at ha; subst a; trivial
  · exact checked1093
theorem derived1093 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1093 := by
  apply localUnsat_implies_entails f1093 [c1083, c1088, c355, c1092, c1091, c272, c734, c228, c21, c268, c807] c1093 unsat1093 (by rfl) a
  have h0 : Entails.eval a c1083 := derived1083 a h
  have h1 : Entails.eval a c1088 := derived1088 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c1092 := derived1092 a h
  have h4 : Entails.eval a c1091 := derived1091 a h
  have h5 : Entails.eval a c272 := h 271 (by decide)
  have h6 : Entails.eval a c734 := derived734 a h
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c807 := derived807 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1094 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨37, by decide⟩, true), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1094 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c228, some c117, some c21, some c268, some c807, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1094 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1094 : lratChecker f1094 p1094 = .success := by decide +kernel
theorem unsat1094 : Unsatisfiable (PosFin 57) f1094 := by
  apply lratCheckerSound f1094 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1094
  · intro a ha; simp [p1094] at ha; subst a; trivial
  · exact checked1094
theorem derived1094 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1094 := by
  apply localUnsat_implies_entails f1094 [c272, c228, c117, c21, c268, c807] c1094 unsat1094 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c228 := h 227 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c807 := derived807 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1095 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨37, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1095 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c21, some c1, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false))]
def p1095 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1095 : lratChecker f1095 p1095 = .success := by decide +kernel
theorem unsat1095 : Unsatisfiable (PosFin 57) f1095 := by
  apply lratCheckerSound f1095 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1095
  · intro a ha; simp [p1095] at ha; subst a; trivial
  · exact checked1095
theorem derived1095 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1095 := by
  apply localUnsat_implies_entails f1095 [c117, c21, c1] c1095 unsat1095 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1096 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨19, by decide⟩, true), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1096 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1092, some c26, some c631, some c797, some c75, some c110, some c107, some c30, some c64, some c854, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1096 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1096 : lratChecker f1096 p1096 = .success := by decide +kernel
theorem unsat1096 : Unsatisfiable (PosFin 57) f1096 := by
  apply lratCheckerSound f1096 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1096
  · intro a ha; simp [p1096] at ha; subst a; trivial
  · exact checked1096
theorem derived1096 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1096 := by
  apply localUnsat_implies_entails f1096 [c1092, c26, c631, c797, c75, c110, c107, c30, c64, c854] c1096 unsat1096 (by rfl) a
  have h0 : Entails.eval a c1092 := derived1092 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c631 := derived631 a h
  have h3 : Entails.eval a c797 := derived797 a h
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c854 := derived854 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1097 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1097 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1093, some c1077, some c353, some c355, some c1092, some c631, some c1094, some c115, some c26, some c1095, some c1096, some c1, some c105, some c145, some c841, some c222, some c47, some c60, some c319, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1097 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1097 : lratChecker f1097 p1097 = .success := by decide +kernel
theorem unsat1097 : Unsatisfiable (PosFin 57) f1097 := by
  apply lratCheckerSound f1097 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1097
  · intro a ha; simp [p1097] at ha; subst a; trivial
  · exact checked1097
theorem derived1097 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1097 := by
  apply localUnsat_implies_entails f1097 [c1093, c1077, c353, c355, c1092, c631, c1094, c115, c26, c1095, c1096, c1, c105, c145, c841, c222, c47, c60, c319] c1097 unsat1097 (by rfl) a
  have h0 : Entails.eval a c1093 := derived1093 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c1092 := derived1092 a h
  have h5 : Entails.eval a c631 := derived631 a h
  have h6 : Entails.eval a c1094 := derived1094 a h
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c1095 := derived1095 a h
  have h10 : Entails.eval a c1096 := derived1096 a h
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c105 := h 104 (by decide)
  have h13 : Entails.eval a c145 := h 144 (by decide)
  have h14 : Entails.eval a c841 := derived841 a h
  have h15 : Entails.eval a c222 := h 221 (by decide)
  have h16 : Entails.eval a c47 := h 46 (by decide)
  have h17 : Entails.eval a c60 := h 59 (by decide)
  have h18 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1098 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1098 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c26, some c462, some c1095, some c797, some c222, some c1, some c145, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1098 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1098 : lratChecker f1098 p1098 = .success := by decide +kernel
theorem unsat1098 : Unsatisfiable (PosFin 57) f1098 := by
  apply lratCheckerSound f1098 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1098
  · intro a ha; simp [p1098] at ha; subst a; trivial
  · exact checked1098
theorem derived1098 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1098 := by
  apply localUnsat_implies_entails f1098 [c631, c26, c462, c1095, c797, c222, c1, c145] c1098 unsat1098 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c462 := derived462 a h
  have h3 : Entails.eval a c1095 := derived1095 a h
  have h4 : Entails.eval a c797 := derived797 a h
  have h5 : Entails.eval a c222 := h 221 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1099 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1099 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1097, some c1093, some c1077, some c1084, some c1098, some c265, some c267, some c1092, some c117, some c31, some c135, some c354, some c808, some c110, some c16, some c76, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1099 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1099 : lratChecker f1099 p1099 = .success := by decide +kernel
theorem unsat1099 : Unsatisfiable (PosFin 57) f1099 := by
  apply lratCheckerSound f1099 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1099
  · intro a ha; simp [p1099] at ha; subst a; trivial
  · exact checked1099
theorem derived1099 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1099 := by
  apply localUnsat_implies_entails f1099 [c1097, c1093, c1077, c1084, c1098, c265, c267, c1092, c117, c31, c135, c354, c808, c110, c16, c76] c1099 unsat1099 (by rfl) a
  have h0 : Entails.eval a c1097 := derived1097 a h
  have h1 : Entails.eval a c1093 := derived1093 a h
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1084 := derived1084 a h
  have h4 : Entails.eval a c1098 := derived1098 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c1092 := derived1092 a h
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c135 := h 134 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c808 := derived808 a h
  have h13 : Entails.eval a c110 := h 109 (by decide)
  have h14 : Entails.eval a c16 := h 15 (by decide)
  have h15 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1100 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1100 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c31, some c135, some c8, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1100 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1100 : lratChecker f1100 p1100 = .success := by decide +kernel
theorem unsat1100 : Unsatisfiable (PosFin 57) f1100 := by
  apply lratCheckerSound f1100 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1100
  · intro a ha; simp [p1100] at ha; subst a; trivial
  · exact checked1100
theorem derived1100 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1100 := by
  apply localUnsat_implies_entails f1100 [c31, c135, c8] c1100 unsat1100 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1101 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1101 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1093, some c1099, some c1079, some c114, some c267, some c1100, some c265, some c1097, some c110, some c8, some c120, some c354, some c906, some c76, some c70, some c42, some c789, some c359, some c210, some c54, some c384, some c219, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1101 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1101 : lratChecker f1101 p1101 = .success := by decide +kernel
theorem unsat1101 : Unsatisfiable (PosFin 57) f1101 := by
  apply lratCheckerSound f1101 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1101
  · intro a ha; simp [p1101] at ha; subst a; trivial
  · exact checked1101
theorem derived1101 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1101 := by
  apply localUnsat_implies_entails f1101 [c1077, c1093, c1099, c1079, c114, c267, c1100, c265, c1097, c110, c8, c120, c354, c906, c76, c70, c42, c789, c359, c210, c54, c384, c219] c1101 unsat1101 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1093 := derived1093 a h
  have h2 : Entails.eval a c1099 := derived1099 a h
  have h3 : Entails.eval a c1079 := derived1079 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c267 := h 266 (by decide)
  have h6 : Entails.eval a c1100 := derived1100 a h
  have h7 : Entails.eval a c265 := h 264 (by decide)
  have h8 : Entails.eval a c1097 := derived1097 a h
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c120 := h 119 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c906 := derived906 a h
  have h14 : Entails.eval a c76 := h 75 (by decide)
  have h15 : Entails.eval a c70 := h 69 (by decide)
  have h16 : Entails.eval a c42 := h 41 (by decide)
  have h17 : Entails.eval a c789 := derived789 a h
  have h18 : Entails.eval a c359 := h 358 (by decide)
  have h19 : Entails.eval a c210 := h 209 (by decide)
  have h20 : Entails.eval a c54 := h 53 (by decide)
  have h21 : Entails.eval a c384 := derived384 a h
  have h22 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1102 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨19, by decide⟩, false), (⟨17, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1102 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c820, some c219, some c211, some c816, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1102 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1102 : lratChecker f1102 p1102 = .success := by decide +kernel
theorem unsat1102 : Unsatisfiable (PosFin 57) f1102 := by
  apply lratCheckerSound f1102 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1102
  · intro a ha; simp [p1102] at ha; subst a; trivial
  · exact checked1102
theorem derived1102 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1102 := by
  apply localUnsat_implies_entails f1102 [c820, c219, c211, c816] c1102 unsat1102 (by rfl) a
  have h0 : Entails.eval a c820 := derived820 a h
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c816 := derived816 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1103 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1103 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1099, some c1079, some c114, some c1097, some c1093, some c1077, some c265, some c267, some c1100, some c1101, some c24, some c35, some c33, some c354, some c906, some c1102, some c139, some c206, some c166, some c146, some c359, some c221, some c40, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1103 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1103 : lratChecker f1103 p1103 = .success := by decide +kernel
theorem unsat1103 : Unsatisfiable (PosFin 57) f1103 := by
  apply lratCheckerSound f1103 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1103
  · intro a ha; simp [p1103] at ha; subst a; trivial
  · exact checked1103
theorem derived1103 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1103 := by
  apply localUnsat_implies_entails f1103 [c1099, c1079, c114, c1097, c1093, c1077, c265, c267, c1100, c1101, c24, c35, c33, c354, c906, c1102, c139, c206, c166, c146, c359, c221, c40] c1103 unsat1103 (by rfl) a
  have h0 : Entails.eval a c1099 := derived1099 a h
  have h1 : Entails.eval a c1079 := derived1079 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c1097 := derived1097 a h
  have h4 : Entails.eval a c1093 := derived1093 a h
  have h5 : Entails.eval a c1077 := derived1077 a h
  have h6 : Entails.eval a c265 := h 264 (by decide)
  have h7 : Entails.eval a c267 := h 266 (by decide)
  have h8 : Entails.eval a c1100 := derived1100 a h
  have h9 : Entails.eval a c1101 := derived1101 a h
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c354 := h 353 (by decide)
  have h14 : Entails.eval a c906 := derived906 a h
  have h15 : Entails.eval a c1102 := derived1102 a h
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c206 := h 205 (by decide)
  have h18 : Entails.eval a c166 := h 165 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c359 := h 358 (by decide)
  have h21 : Entails.eval a c221 := h 220 (by decide)
  have h22 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1104 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨38, by decide⟩, true), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨39, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1104 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c206, some c203, some c172, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false))]
def p1104 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1104 : lratChecker f1104 p1104 = .success := by decide +kernel
theorem unsat1104 : Unsatisfiable (PosFin 57) f1104 := by
  apply lratCheckerSound f1104 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1104
  · intro a ha; simp [p1104] at ha; subst a; trivial
  · exact checked1104
theorem derived1104 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1104 := by
  apply localUnsat_implies_entails f1104 [c206, c203, c172] c1104 unsat1104 (by rfl) a
  have h0 : Entails.eval a c206 := h 205 (by decide)
  have h1 : Entails.eval a c203 := h 202 (by decide)
  have h2 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1105 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1105 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c631, some c114, some c1077, some c24, some c35, some c354, some c1104, some c139, some c128, some c820, some c201, some c324, some c219, some c172, some c237, some c155, some c816, some c908, some c292, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1105 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1105 : lratChecker f1105 p1105 = .success := by decide +kernel
theorem unsat1105 : Unsatisfiable (PosFin 57) f1105 := by
  apply lratCheckerSound f1105 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1105
  · intro a ha; simp [p1105] at ha; subst a; trivial
  · exact checked1105
theorem derived1105 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1105 := by
  apply localUnsat_implies_entails f1105 [c272, c631, c114, c1077, c24, c35, c354, c1104, c139, c128, c820, c201, c324, c219, c172, c237, c155, c816, c908, c292] c1105 unsat1105 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c1104 := derived1104 a h
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c820 := derived820 a h
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c324 := h 323 (by decide)
  have h13 : Entails.eval a c219 := h 218 (by decide)
  have h14 : Entails.eval a c172 := h 171 (by decide)
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c816 := derived816 a h
  have h18 : Entails.eval a c908 := derived908 a h
  have h19 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1106 : DefaultClause 57 := directClause [(⟨14, by decide⟩, false), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1106 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c7, some c70, some c42, some c359, some c839, some c384, some c219, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1106 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1106 : lratChecker f1106 p1106 = .success := by decide +kernel
theorem unsat1106 : Unsatisfiable (PosFin 57) f1106 := by
  apply lratCheckerSound f1106 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1106
  · intro a ha; simp [p1106] at ha; subst a; trivial
  · exact checked1106
theorem derived1106 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1106 := by
  apply localUnsat_implies_entails f1106 [c1077, c7, c70, c42, c359, c839, c384, c219] c1106 unsat1106 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c359 := h 358 (by decide)
  have h5 : Entails.eval a c839 := derived839 a h
  have h6 : Entails.eval a c384 := derived384 a h
  have h7 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1107 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨16, by decide⟩, true), (⟨24, by decide⟩, false), (⟨19, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1107 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c906, some c1106, some c166, some c172, some c146, some c359, some c201, some c223, some c40, some c159, some c155, some c319, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1107 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1107 : lratChecker f1107 p1107 = .success := by decide +kernel
theorem unsat1107 : Unsatisfiable (PosFin 57) f1107 := by
  apply lratCheckerSound f1107 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1107
  · intro a ha; simp [p1107] at ha; subst a; trivial
  · exact checked1107
theorem derived1107 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1107 := by
  apply localUnsat_implies_entails f1107 [c906, c1106, c166, c172, c146, c359, c201, c223, c40, c159, c155, c319] c1107 unsat1107 (by rfl) a
  have h0 : Entails.eval a c906 := derived906 a h
  have h1 : Entails.eval a c1106 := derived1106 a h
  have h2 : Entails.eval a c166 := h 165 (by decide)
  have h3 : Entails.eval a c172 := h 171 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c223 := h 222 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1108 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1108 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1093, some c1097, some c1099, some c1079, some c1103, some c1105, some c631, some c114, some c1107, some c354, some c167, some c73, some c359, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1108 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1108 : lratChecker f1108 p1108 = .success := by decide +kernel
theorem unsat1108 : Unsatisfiable (PosFin 57) f1108 := by
  apply lratCheckerSound f1108 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1108
  · intro a ha; simp [p1108] at ha; subst a; trivial
  · exact checked1108
theorem derived1108 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1108 := by
  apply localUnsat_implies_entails f1108 [c1093, c1097, c1099, c1079, c1103, c1105, c631, c114, c1107, c354, c167, c73, c359] c1108 unsat1108 (by rfl) a
  have h0 : Entails.eval a c1093 := derived1093 a h
  have h1 : Entails.eval a c1097 := derived1097 a h
  have h2 : Entails.eval a c1099 := derived1099 a h
  have h3 : Entails.eval a c1079 := derived1079 a h
  have h4 : Entails.eval a c1103 := derived1103 a h
  have h5 : Entails.eval a c1105 := derived1105 a h
  have h6 : Entails.eval a c631 := derived631 a h
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c1107 := derived1107 a h
  have h9 : Entails.eval a c354 := h 353 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c359 := h 358 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1109 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1109 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c631, some c1099, some c1079, some c114, some c1097, some c1093, some c1105, some c1108, some c203, some c1104, some c147, some c354, some c224, some c44, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1109 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1109 : lratChecker f1109 p1109 = .success := by decide +kernel
theorem unsat1109 : Unsatisfiable (PosFin 57) f1109 := by
  apply lratCheckerSound f1109 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1109
  · intro a ha; simp [p1109] at ha; subst a; trivial
  · exact checked1109
theorem derived1109 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1109 := by
  apply localUnsat_implies_entails f1109 [c1103, c631, c1099, c1079, c114, c1097, c1093, c1105, c1108, c203, c1104, c147, c354, c224, c44] c1109 unsat1109 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1099 := derived1099 a h
  have h3 : Entails.eval a c1079 := derived1079 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c1097 := derived1097 a h
  have h6 : Entails.eval a c1093 := derived1093 a h
  have h7 : Entails.eval a c1105 := derived1105 a h
  have h8 : Entails.eval a c1108 := derived1108 a h
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c1104 := derived1104 a h
  have h11 : Entails.eval a c147 := h 146 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c224 := h 223 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1110 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨16, by decide⟩, true), (⟨6, by decide⟩, true), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨11, by decide⟩, true), (⟨4, by decide⟩, true), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1110 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c685, some c167, some c148, some c277, some c359, some c318, some c40, some c58, some c316, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1110 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1110 : lratChecker f1110 p1110 = .success := by decide +kernel
theorem unsat1110 : Unsatisfiable (PosFin 57) f1110 := by
  apply lratCheckerSound f1110 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1110
  · intro a ha; simp [p1110] at ha; subst a; trivial
  · exact checked1110
theorem derived1110 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1110 := by
  apply localUnsat_implies_entails f1110 [c1077, c685, c167, c148, c277, c359, c318, c40, c58, c316] c1110 unsat1110 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c685 := derived685 a h
  have h2 : Entails.eval a c167 := h 166 (by decide)
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c359 := h 358 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c58 := h 57 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1111 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1111 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1103, some c631, some c1099, some c1079, some c114, some c1097, some c1093, some c272, some c1109, some c110, some c8, some c1110, some c354, some c1106, some c1107, some c172, some c139, some c201, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1111 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1111 : lratChecker f1111 p1111 = .success := by decide +kernel
theorem unsat1111 : Unsatisfiable (PosFin 57) f1111 := by
  apply lratCheckerSound f1111 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1111
  · intro a ha; simp [p1111] at ha; subst a; trivial
  · exact checked1111
theorem derived1111 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1111 := by
  apply localUnsat_implies_entails f1111 [c1103, c631, c1099, c1079, c114, c1097, c1093, c272, c1109, c110, c8, c1110, c354, c1106, c1107, c172, c139, c201] c1111 unsat1111 (by rfl) a
  have h0 : Entails.eval a c1103 := derived1103 a h
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1099 := derived1099 a h
  have h3 : Entails.eval a c1079 := derived1079 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c1097 := derived1097 a h
  have h6 : Entails.eval a c1093 := derived1093 a h
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c1109 := derived1109 a h
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c8 := h 7 (by decide)
  have h11 : Entails.eval a c1110 := derived1110 a h
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c1106 := derived1106 a h
  have h14 : Entails.eval a c1107 := derived1107 a h
  have h15 : Entails.eval a c172 := h 171 (by decide)
  have h16 : Entails.eval a c139 := h 138 (by decide)
  have h17 : Entails.eval a c201 := h 200 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1112 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1112 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1093, some c1097, some c1099, some c1079, some c114, some c1103, some c631, some c1111, some c115, some c1100, some c26, some c359, some c462, some c72, some c224, some c107, some c105, some c63, some c59, some c320, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1112 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1112 : lratChecker f1112 p1112 = .success := by decide +kernel
theorem unsat1112 : Unsatisfiable (PosFin 57) f1112 := by
  apply lratCheckerSound f1112 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1112
  · intro a ha; simp [p1112] at ha; subst a; trivial
  · exact checked1112
theorem derived1112 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1112 := by
  apply localUnsat_implies_entails f1112 [c1077, c1093, c1097, c1099, c1079, c114, c1103, c631, c1111, c115, c1100, c26, c359, c462, c72, c224, c107, c105, c63, c59, c320] c1112 unsat1112 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1093 := derived1093 a h
  have h2 : Entails.eval a c1097 := derived1097 a h
  have h3 : Entails.eval a c1099 := derived1099 a h
  have h4 : Entails.eval a c1079 := derived1079 a h
  have h5 : Entails.eval a c114 := h 113 (by decide)
  have h6 : Entails.eval a c1103 := derived1103 a h
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c1111 := derived1111 a h
  have h9 : Entails.eval a c115 := h 114 (by decide)
  have h10 : Entails.eval a c1100 := derived1100 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c359 := h 358 (by decide)
  have h13 : Entails.eval a c462 := derived462 a h
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c224 := h 223 (by decide)
  have h16 : Entails.eval a c107 := h 106 (by decide)
  have h17 : Entails.eval a c105 := h 104 (by decide)
  have h18 : Entails.eval a c63 := h 62 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1113 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨37, by decide⟩, false), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, false), (⟨6, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1113 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c115, some c1100, some c359, some c792, some c267, some c144, some c116, some c631, some c26, some c658, some c201, some c203, some c354, some c667, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1113 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1113 : lratChecker f1113 p1113 = .success := by decide +kernel
theorem unsat1113 : Unsatisfiable (PosFin 57) f1113 := by
  apply lratCheckerSound f1113 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1113
  · intro a ha; simp [p1113] at ha; subst a; trivial
  · exact checked1113
theorem derived1113 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1113 := by
  apply localUnsat_implies_entails f1113 [c115, c1100, c359, c792, c267, c144, c116, c631, c26, c658, c201, c203, c354, c667] c1113 unsat1113 (by rfl) a
  have h0 : Entails.eval a c115 := h 114 (by decide)
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c792 := derived792 a h
  have h4 : Entails.eval a c267 := h 266 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c658 := derived658 a h
  have h10 : Entails.eval a c201 := h 200 (by decide)
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c667 := derived667 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1114 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨8, by decide⟩, true), (⟨6, by decide⟩, true), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c70, some c354, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 57) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c71, c70, c354] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c70 := h 69 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨39, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1112, some c109, some c1114, some c6, some c1113, some c359, some c144, some c116, some c658, some c217, some c354, some c59, some c58, some c24, some c224, some c318, some c277, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 57) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c1077, c1112, c109, c1114, c6, c1113, c359, c144, c116, c658, c217, c354, c59, c58, c24, c224, c318, c277] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1112 := derived1112 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c1114 := derived1114 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1113 := derived1113 a h
  have h6 : Entails.eval a c359 := h 358 (by decide)
  have h7 : Entails.eval a c144 := h 143 (by decide)
  have h8 : Entails.eval a c116 := h 115 (by decide)
  have h9 : Entails.eval a c658 := derived658 a h
  have h10 : Entails.eval a c217 := h 216 (by decide)
  have h11 : Entails.eval a c354 := h 353 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c58 := h 57 (by decide)
  have h14 : Entails.eval a c24 := h 23 (by decide)
  have h15 : Entails.eval a c224 := h 223 (by decide)
  have h16 : Entails.eval a c318 := h 317 (by decide)
  have h17 : Entails.eval a c277 := h 276 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨37, by decide⟩, true), (⟨11, by decide⟩, true), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c117, some c21, some c820, some c822, some c219, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p1116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 57) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c272, c117, c21, c820, c822, c219] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c820 := derived820 a h
  have h4 : Entails.eval a c822 := derived822 a h
  have h5 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨11, by decide⟩, true), (⟨39, by decide⟩, true), (⟨10, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1116, some c1098, some c1100, some c267, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 57) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c1116, c1098, c1100, c267] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c1116 := derived1116 a h
  have h1 : Entails.eval a c1098 := derived1098 a h
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c267 := h 266 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c631, some c272, some c219, some c277, some c147, some c213, some c316, some c201, some c144, some c125, some c532, some c332, some c237, some c181, some c84, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 57) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c631, c272, c219, c277, c147, c213, c316, c201, c144, c125, c532, c332, c237, c181, c84] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c631 := derived631 a h
  have h1 : Entails.eval a c272 := h 271 (by decide)
  have h2 : Entails.eval a c219 := h 218 (by decide)
  have h3 : Entails.eval a c277 := h 276 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c213 := h 212 (by decide)
  have h6 : Entails.eval a c316 := h 315 (by decide)
  have h7 : Entails.eval a c201 := h 200 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  have h10 : Entails.eval a c532 := derived532 a h
  have h11 : Entails.eval a c332 := h 331 (by decide)
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c181 := h 180 (by decide)
  have h14 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨37, by decide⟩, false), (⟨11, by decide⟩, true), (⟨39, by decide⟩, true), (⟨12, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1112, some c109, some c1077, some c631, some c1118, some c58, some c155, some c840, some c314, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 57) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c1112, c109, c1077, c631, c1118, c58, c155, c840, c314] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c1112 := derived1112 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c1118 := derived1118 a h
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c840 := derived840 a h
  have h8 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨39, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1112, some c6, some c109, some c1077, some c1117, some c1113, some c1115, some c8, some c1119, some c267, some c120, some c137, some c354, some c70, some c658, some c359, some c144, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 57) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c1112, c6, c109, c1077, c1117, c1113, c1115, c8, c1119, c267, c120, c137, c354, c70, c658, c359, c144] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c1112 := derived1112 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c1077 := derived1077 a h
  have h4 : Entails.eval a c1117 := derived1117 a h
  have h5 : Entails.eval a c1113 := derived1113 a h
  have h6 : Entails.eval a c1115 := derived1115 a h
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c1119 := derived1119 a h
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c137 := h 136 (by decide)
  have h12 : Entails.eval a c354 := h 353 (by decide)
  have h13 : Entails.eval a c70 := h 69 (by decide)
  have h14 : Entails.eval a c658 := derived658 a h
  have h15 : Entails.eval a c359 := h 358 (by decide)
  have h16 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨37, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨6, by decide⟩, true), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c120, some c139, some c354, some c208, some c70, some c792, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 57) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c120, c139, c354, c208, c70, c792] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c120 := h 119 (by decide)
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  have h3 : Entails.eval a c208 := h 207 (by decide)
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c792 := derived792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c272, some c1120, some c1112, some c6, some c109, some c1077, some c8, some c1121, some c267, some c631, some c1118, some c734, some c201, some c39, some c792, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 57) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c272, c1120, c1112, c6, c109, c1077, c8, c1121, c267, c631, c1118, c734, c201, c39, c792] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c272 := h 271 (by decide)
  have h1 : Entails.eval a c1120 := derived1120 a h
  have h2 : Entails.eval a c1112 := derived1112 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c1077 := derived1077 a h
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c1121 := derived1121 a h
  have h8 : Entails.eval a c267 := h 266 (by decide)
  have h9 : Entails.eval a c631 := derived631 a h
  have h10 : Entails.eval a c1118 := derived1118 a h
  have h11 : Entails.eval a c734 := derived734 a h
  have h12 : Entails.eval a c201 := h 200 (by decide)
  have h13 : Entails.eval a c39 := h 38 (by decide)
  have h14 : Entails.eval a c792 := derived792 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1112, some c6, some c109, some c1077, some c1122, some c1114, some c359, some c792, some c144, some c116, some c208, some c658, some c734, some c354, some c267, some c24, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 57) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c1120, c1112, c6, c109, c1077, c1122, c1114, c359, c792, c144, c116, c208, c658, c734, c354, c267, c24] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1112 := derived1112 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1122 := derived1122 a h
  have h6 : Entails.eval a c1114 := derived1114 a h
  have h7 : Entails.eval a c359 := h 358 (by decide)
  have h8 : Entails.eval a c792 := derived792 a h
  have h9 : Entails.eval a c144 := h 143 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  have h12 : Entails.eval a c658 := derived658 a h
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨39, by decide⟩, true), (⟨10, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨23, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1112, some c6, some c109, some c1077, some c1123, some c19, some c30, some c359, some c792, some c144, some c116, some c208, some c658, some c221, some c1081, some c354, some c58, some c64, some c169, some c320, some c206, some c158, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 57) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c1120, c1112, c6, c109, c1077, c1123, c19, c30, c359, c792, c144, c116, c208, c658, c221, c1081, c354, c58, c64, c169, c320, c206, c158] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1112 := derived1112 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c1077 := derived1077 a h
  have h5 : Entails.eval a c1123 := derived1123 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c792 := derived792 a h
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c116 := h 115 (by decide)
  have h12 : Entails.eval a c208 := h 207 (by decide)
  have h13 : Entails.eval a c658 := derived658 a h
  have h14 : Entails.eval a c221 := h 220 (by decide)
  have h15 : Entails.eval a c1081 := derived1081 a h
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c58 := h 57 (by decide)
  have h18 : Entails.eval a c64 := h 63 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c320 := h 319 (by decide)
  have h21 : Entails.eval a c206 := h 205 (by decide)
  have h22 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1098, some c1087, some c265, some c117, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 57) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c1077, c1098, c1087, c265, c117] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1098 := derived1098 a h
  have h2 : Entails.eval a c1087 := derived1087 a h
  have h3 : Entails.eval a c265 := h 264 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨34, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1125, some c355, some c1092, some c1091, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 57) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c1125, c355, c1092, c1091] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c1125 := derived1125 a h
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c1092 := derived1092 a h
  have h3 : Entails.eval a c1091 := derived1091 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨39, by decide⟩, false), (⟨23, by decide⟩, true), (⟨35, by decide⟩, false), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c631, some c1089, some c127, some c323, some c331, some c238, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 57) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c355, c631, c1089, c127, c323, c331, c238] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c631 := derived631 a h
  have h2 : Entails.eval a c1089 := derived1089 a h
  have h3 : Entails.eval a c127 := h 126 (by decide)
  have h4 : Entails.eval a c323 := h 322 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c164, some c171, some c8, some c206, some c31, some c140, some c266, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 57) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c1077, c164, c171, c8, c206, c31, c140, c266] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c164 := h 163 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c206 := h 205 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c140 := h 139 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 57 := directClause [(⟨16, by decide⟩, false), (⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨17, by decide⟩, false), (⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c8, some c206, some c31, some c140, some c266, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 57) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c8, c206, c31, c140, c266] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨15, by decide⟩, true), (⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1129, some c120, some c266, some c140, some c30, some c7, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 57) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c1129, c120, c266, c140, c30, c7] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c1129 := derived1129 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c140 := h 139 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨28, by decide⟩, true), (⟨17, by decide⟩, false), (⟨40, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c202, some c2, some c148, some c120, some c55, some c212, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false))]
def p1131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 57) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c202, c2, c148, c120, c55, c212] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c202 := h 201 (by decide)
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨39, by decide⟩, false), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c19, some c1126, some c1127, some c355, some c127, some c323, some c331, some c1128, some c207, some c136, some c1130, some c114, some c666, some c269, some c140, some c30, some c242, some c109, some c83, some c1131, some c173, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 57) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c1077, c19, c1126, c1127, c355, c127, c323, c331, c1128, c207, c136, c1130, c114, c666, c269, c140, c30, c242, c109, c83, c1131, c173] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c1126 := derived1126 a h
  have h3 : Entails.eval a c1127 := derived1127 a h
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c323 := h 322 (by decide)
  have h7 : Entails.eval a c331 := h 330 (by decide)
  have h8 : Entails.eval a c1128 := derived1128 a h
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c1130 := derived1130 a h
  have h12 : Entails.eval a c114 := h 113 (by decide)
  have h13 : Entails.eval a c666 := derived666 a h
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c140 := h 139 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c242 := h 241 (by decide)
  have h18 : Entails.eval a c109 := h 108 (by decide)
  have h19 : Entails.eval a c83 := h 82 (by decide)
  have h20 : Entails.eval a c1131 := derived1131 a h
  have h21 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1126, some c1077, some c19, some c355, some c1127, some c1132, some c208, some c1089, some c164, some c145, some c117, some c171, some c204, some c209, some c8, some c206, some c151, some c31, some c170, some c220, some c266, some c116, some c124, some c126, some c333, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 57) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c1126, c1077, c19, c355, c1127, c1132, c208, c1089, c164, c145, c117, c171, c204, c209, c8, c206, c151, c31, c170, c220, c266, c116, c124, c126, c333] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c1126 := derived1126 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c355 := h 354 (by decide)
  have h4 : Entails.eval a c1127 := derived1127 a h
  have h5 : Entails.eval a c1132 := derived1132 a h
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c1089 := derived1089 a h
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  have h14 : Entails.eval a c8 := h 7 (by decide)
  have h15 : Entails.eval a c206 := h 205 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  have h17 : Entails.eval a c31 := h 30 (by decide)
  have h18 : Entails.eval a c170 := h 169 (by decide)
  have h19 : Entails.eval a c220 := h 219 (by decide)
  have h20 : Entails.eval a c266 := h 265 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  have h22 : Entails.eval a c124 := h 123 (by decide)
  have h23 : Entails.eval a c126 := h 125 (by decide)
  have h24 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨25, by decide⟩, true), (⟨10, by decide⟩, false), (⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c208, some c145, some c1089, some c171, some c151, some c8, some c319, some c75, some c54, some c105, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 57) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c204, c208, c145, c1089, c171, c151, c8, c319, c75, c54, c105] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c1089 := derived1089 a h
  have h4 : Entails.eval a c171 := h 170 (by decide)
  have h5 : Entails.eval a c151 := h 150 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c319 := h 318 (by decide)
  have h8 : Entails.eval a c75 := h 74 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1126, some c1133, some c23, some c229, some c119, some c208, some c1080, some c164, some c145, some c117, some c204, some c209, some c1134, some c354, some c906, some c170, some c266, some c269, some c206, some c137, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 57) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c1077, c1126, c1133, c23, c229, c119, c208, c1080, c164, c145, c117, c204, c209, c1134, c354, c906, c170, c266, c269, c206, c137] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1126 := derived1126 a h
  have h2 : Entails.eval a c1133 := derived1133 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c119 := h 118 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c1080 := derived1080 a h
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c204 := h 203 (by decide)
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c1134 := derived1134 a h
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c906 := derived906 a h
  have h16 : Entails.eval a c170 := h 169 (by decide)
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c269 := h 268 (by decide)
  have h19 : Entails.eval a c206 := h 205 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨23, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1135, some c1077, some c23, some c229, some c119, some c268, some c208, some c232, some c164, some c145, some c117, some c734, some c209, some c218, some c1134, some c39, some c354, some c170, some c693, some c206, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 57) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c1135, c1077, c23, c229, c119, c268, c208, c232, c164, c145, c117, c734, c209, c218, c1134, c39, c354, c170, c693, c206] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c1135 := derived1135 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c164 := h 163 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c734 := derived734 a h
  have h12 : Entails.eval a c209 := h 208 (by decide)
  have h13 : Entails.eval a c218 := h 217 (by decide)
  have h14 : Entails.eval a c1134 := derived1134 a h
  have h15 : Entails.eval a c39 := h 38 (by decide)
  have h16 : Entails.eval a c354 := h 353 (by decide)
  have h17 : Entails.eval a c170 := h 169 (by decide)
  have h18 : Entails.eval a c693 := derived693 a h
  have h19 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨17, by decide⟩, false), (⟨40, by decide⟩, true), (⟨23, by decide⟩, true), (⟨19, by decide⟩, false), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c208, some c1089, some c164, some c145, some c117, some c204, some c209, some c218, some c271, some c124, some c1134, some c151, some c47, some c32, some c296, some c189, some c258, some c82, some c364, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 57) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c1077, c208, c1089, c164, c145, c117, c204, c209, c218, c271, c124, c1134, c151, c47, c32, c296, c189, c258, c82, c364] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c1089 := derived1089 a h
  have h3 : Entails.eval a c164 := h 163 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c204 := h 203 (by decide)
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c218 := h 217 (by decide)
  have h9 : Entails.eval a c271 := h 270 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c1134 := derived1134 a h
  have h12 : Entails.eval a c151 := h 150 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c32 := h 31 (by decide)
  have h15 : Entails.eval a c296 := h 295 (by decide)
  have h16 : Entails.eval a c189 := h 188 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c82 := h 81 (by decide)
  have h19 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨19, by decide⟩, false), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c271, some c228, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 57) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c268, c271, c228] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 57 := directClause [(⟨12, by decide⟩, false), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c207, some c164, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 57) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c204, c207, c164] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1139, some c1135, some c1138, some c1136, some c355, some c136, some c208, some c1137, some c734, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 57) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c1139, c1135, c1138, c1136, c355, c136, c208, c1137, c734] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c1139 := derived1139 a h
  have h1 : Entails.eval a c1135 := derived1135 a h
  have h2 : Entails.eval a c1138 := derived1138 a h
  have h3 : Entails.eval a c1136 := derived1136 a h
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c1137 := derived1137 a h
  have h8 : Entails.eval a c734 := derived734 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨45, by decide⟩, true), (⟨6, by decide⟩, true), (⟨21, by decide⟩, true), (⟨44, by decide⟩, false), (⟨36, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c246, some c333, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true))]
def p1141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 57) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c22, c246, c333] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c246 := h 245 (by decide)
  have h2 : Entails.eval a c333 := h 332 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1135, some c1138, some c1139, some c116, some c124, some c1140, some c1112, some c272, some c109, some c228, some c117, some c21, some c208, some c88, some c1141, some c554, some c270, some c142, some c235, some c137, some c354, some c355, some c206, some c172, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 57) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c1077, c1135, c1138, c1139, c116, c124, c1140, c1112, c272, c109, c228, c117, c21, c208, c88, c1141, c554, c270, c142, c235, c137, c354, c355, c206, c172] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1135 := derived1135 a h
  have h2 : Entails.eval a c1138 := derived1138 a h
  have h3 : Entails.eval a c1139 := derived1139 a h
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c1140 := derived1140 a h
  have h7 : Entails.eval a c1112 := derived1112 a h
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c109 := h 108 (by decide)
  have h10 : Entails.eval a c228 := h 227 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c208 := h 207 (by decide)
  have h14 : Entails.eval a c88 := h 87 (by decide)
  have h15 : Entails.eval a c1141 := derived1141 a h
  have h16 : Entails.eval a c554 := derived554 a h
  have h17 : Entails.eval a c270 := h 269 (by decide)
  have h18 : Entails.eval a c142 := h 141 (by decide)
  have h19 : Entails.eval a c235 := h 234 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c354 := h 353 (by decide)
  have h22 : Entails.eval a c355 := h 354 (by decide)
  have h23 : Entails.eval a c206 := h 205 (by decide)
  have h24 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨36, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c554, some c734, some c22, some c267, some c354, some c233, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 57) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c554, c734, c22, c267, c354, c233] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c554 := derived554 a h
  have h1 : Entails.eval a c734 := derived734 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c267 := h 266 (by decide)
  have h4 : Entails.eval a c354 := h 353 (by decide)
  have h5 : Entails.eval a c233 := h 232 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨36, by decide⟩, true), (⟨3, by decide⟩, true), (⟨13, by decide⟩, true), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1143, some c30, some c270, some c215, some c233, some c42, some c354, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 57) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c1143, c30, c270, c215, c233, c42, c354] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c1143 := derived1143 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c270 := h 269 (by decide)
  have h3 : Entails.eval a c215 := h 214 (by decide)
  have h4 : Entails.eval a c233 := h 232 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨13, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false), (⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1144, some c268, some c269, some c30, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p1145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 57) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1144, c268, c269, c30] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1142, some c353, some c1077, some c1112, some c1124, some c109, some c142, some c114, some c165, some c1078, some c208, some c359, some c1145, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 57) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1142, c353, c1077, c1112, c1124, c109, c142, c114, c165, c1078, c208, c359, c1145] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1142 := derived1142 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c1112 := derived1112 a h
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c142 := h 141 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c165 := h 164 (by decide)
  have h9 : Entails.eval a c1078 := derived1078 a h
  have h10 : Entails.eval a c208 := h 207 (by decide)
  have h11 : Entails.eval a c359 := h 358 (by decide)
  have h12 : Entails.eval a c1145 := derived1145 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨39, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c232, some c268, some c269, some c30, some c236, some c110, some c109, some c354, some c73, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 57) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c232, c268, c269, c30, c236, c110, c109, c354, c73] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c232 := h 231 (by decide)
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c236 := h 235 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c354 := h 353 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨45, by decide⟩, true), (⟨44, by decide⟩, false), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨13, by decide⟩, true), (⟨37, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c775, some c722, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, false)), some (DefaultClause.unit (⟨44, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true))]
def p1148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 57) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c775, c722] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c775 := derived775 a h
  have h1 : Entails.eval a c722 := derived722 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1149 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1142, some c353, some c1146, some c23, some c229, some c119, some c208, some c1147, some c359, some c19, some c39, some c268, some c734, some c213, some c142, some c204, some c124, some c767, some c1148, some c206, some c7, some c137, some c183, some c70, some c1114, some c266, some c92, some c333, some c248, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 57) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c1077, c1142, c353, c1146, c23, c229, c119, c208, c1147, c359, c19, c39, c268, c734, c213, c142, c204, c124, c767, c1148, c206, c7, c137, c183, c70, c1114, c266, c92, c333, c248] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1142 := derived1142 a h
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c1146 := derived1146 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c229 := h 228 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c1147 := derived1147 a h
  have h9 : Entails.eval a c359 := h 358 (by decide)
  have h10 : Entails.eval a c19 := h 18 (by decide)
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c268 := h 267 (by decide)
  have h13 : Entails.eval a c734 := derived734 a h
  have h14 : Entails.eval a c213 := h 212 (by decide)
  have h15 : Entails.eval a c142 := h 141 (by decide)
  have h16 : Entails.eval a c204 := h 203 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c767 := derived767 a h
  have h19 : Entails.eval a c1148 := derived1148 a h
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c7 := h 6 (by decide)
  have h22 : Entails.eval a c137 := h 136 (by decide)
  have h23 : Entails.eval a c183 := h 182 (by decide)
  have h24 : Entails.eval a c70 := h 69 (by decide)
  have h25 : Entails.eval a c1114 := derived1114 a h
  have h26 : Entails.eval a c266 := h 265 (by decide)
  have h27 : Entails.eval a c92 := h 91 (by decide)
  have h28 : Entails.eval a c333 := h 332 (by decide)
  have h29 : Entails.eval a c248 := h 247 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1149, some c1077, some c980, some c70, some c1114, some c142, some c354, some c8, some c167, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 57) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1149, c1077, c980, c70, c1114, c142, c354, c8, c167] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1149 := derived1149 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c980 := derived980 a h
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c1114 := derived1114 a h
  have h5 : Entails.eval a c142 := h 141 (by decide)
  have h6 : Entails.eval a c354 := h 353 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨29, by decide⟩, false), (⟨26, by decide⟩, true), (⟨32, by decide⟩, false), (⟨13, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c277, some c201, some c320, some c315, some c150, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 57) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c119, c277, c201, c320, c315, c150] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c277 := h 276 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  have h5 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨29, by decide⟩, false), (⟨7, by decide⟩, false), (⟨22, by decide⟩, true), (⟨32, by decide⟩, false), (⟨24, by decide⟩, false), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, false), (⟨37, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c30, some c201, some c14, some c631, some c21, some c212, some c218, some c831, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 57) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c30, c201, c14, c631, c21, c212, c218, c831] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c201 := h 200 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c631 := derived631 a h
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c212 := h 211 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c831 := derived831 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨10, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c8, some c171, some c120, some c148, some c270, some c216, some c36, some c276, some c1151, some c1152, some c127, some c92, some c413, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 57) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1077, c8, c171, c120, c148, c270, c216, c36, c276, c1151, c1152, c127, c92, c413] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c171 := h 170 (by decide)
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c148 := h 147 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  have h9 : Entails.eval a c1151 := derived1151 a h
  have h10 : Entails.eval a c1152 := derived1152 a h
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c413 := derived413 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨10, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c136, some c140, some c205, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 57) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c136, c140, c205] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c136 := h 135 (by decide)
  have h1 : Entails.eval a c140 := h 139 (by decide)
  have h2 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨40, by decide⟩, true), (⟨37, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1153, some c75, some c24, some c44, some c270, some c216, some c30, some c36, some c276, some c1138, some c1154, some c14, some c117, some c171, some c218, some c203, some c150, some c631, some c212, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 57) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1077, c1153, c75, c24, c44, c270, c216, c30, c36, c276, c1138, c1154, c14, c117, c171, c218, c203, c150, c631, c212] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c216 := h 215 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c276 := h 275 (by decide)
  have h10 : Entails.eval a c1138 := derived1138 a h
  have h11 : Entails.eval a c1154 := derived1154 a h
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c171 := h 170 (by decide)
  have h15 : Entails.eval a c218 := h 217 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c150 := h 149 (by decide)
  have h18 : Entails.eval a c631 := derived631 a h
  have h19 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨15, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c270, some c216, some c36, some c148, some c44, some c16, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 57) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c270, c216, c36, c148, c44, c16] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c270 := h 269 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c148 := h 147 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨26, by decide⟩, false), (⟨35, by decide⟩, false), (⟨6, by decide⟩, true), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c36, some c269, some c554, some c123, some c331, some c329, some c244, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 57) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c23, c36, c269, c554, c123, c331, c329, c244] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c269 := h 268 (by decide)
  have h3 : Entails.eval a c554 := derived554 a h
  have h4 : Entails.eval a c123 := h 122 (by decide)
  have h5 : Entails.eval a c331 := h 330 (by decide)
  have h6 : Entails.eval a c329 := h 328 (by decide)
  have h7 : Entails.eval a c244 := h 243 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨7, by decide⟩, false), (⟨26, by decide⟩, false), (⟨40, by decide⟩, true), (⟨6, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1156, some c24, some c120, some c16, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p1158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 57) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c1156, c24, c120, c16] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨35, by decide⟩, false), (⟨6, by decide⟩, true), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨2, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c359, some c1077, some c1155, some c142, some c1157, some c1158, some c119, some c127, some c331, some c123, some c213, some c554, some c58, some c140, some c839, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 57) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c359, c1077, c1155, c142, c1157, c1158, c119, c127, c331, c123, c213, c554, c58, c140, c839] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c359 := h 358 (by decide)
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1155 := derived1155 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c1157 := derived1157 a h
  have h5 : Entails.eval a c1158 := derived1158 a h
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c127 := h 126 (by decide)
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  have h10 : Entails.eval a c213 := h 212 (by decide)
  have h11 : Entails.eval a c554 := derived554 a h
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c140 := h 139 (by decide)
  have h14 : Entails.eval a c839 := derived839 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 57 := directClause [(⟨6, by decide⟩, true), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨2, by decide⟩, false), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1149, some c1077, some c1150, some c359, some c1159, some c354, some c355, some c22, some c76, some c42, some c74, some c119, some c270, some c215, some c14, some c142, some c276, some c117, some c170, some c1100, some c218, some c839, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 57) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c1149, c1077, c1150, c359, c1159, c354, c355, c22, c76, c42, c74, c119, c270, c215, c14, c142, c276, c117, c170, c1100, c218, c839] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c1149 := derived1149 a h
  have h1 : Entails.eval a c1077 := derived1077 a h
  have h2 : Entails.eval a c1150 := derived1150 a h
  have h3 : Entails.eval a c359 := h 358 (by decide)
  have h4 : Entails.eval a c1159 := derived1159 a h
  have h5 : Entails.eval a c354 := h 353 (by decide)
  have h6 : Entails.eval a c355 := h 354 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c215 := h 214 (by decide)
  have h14 : Entails.eval a c14 := h 13 (by decide)
  have h15 : Entails.eval a c142 := h 141 (by decide)
  have h16 : Entails.eval a c276 := h 275 (by decide)
  have h17 : Entails.eval a c117 := h 116 (by decide)
  have h18 : Entails.eval a c170 := h 169 (by decide)
  have h19 : Entails.eval a c1100 := derived1100 a h
  have h20 : Entails.eval a c218 := h 217 (by decide)
  have h21 : Entails.eval a c839 := derived839 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, true), (⟨26, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c276, some c354, some c355, some c236, some c691, some c170, some c909, some c320, some c201, some c150, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 57) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c276, c354, c355, c236, c691, c170, c909, c320, c201, c150] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c236 := h 235 (by decide)
  have h4 : Entails.eval a c691 := derived691 a h
  have h5 : Entails.eval a c170 := h 169 (by decide)
  have h6 : Entails.eval a c909 := derived909 a h
  have h7 : Entails.eval a c320 := h 319 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨26, by decide⟩, true), (⟨7, by decide⟩, false), (⟨14, by decide⟩, true), (⟨15, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c276, some c1161, some c24, some c75, some c270, some c14, some c134, some c138, some c171, some c218, some c521, some c203, some c150, some c209, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 57) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c276, c1161, c24, c75, c270, c14, c134, c138, c171, c218, c521, c203, c150, c209] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c276 := h 275 (by decide)
  have h1 : Entails.eval a c1161 := derived1161 a h
  have h2 : Entails.eval a c24 := h 23 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c270 := h 269 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c171 := h 170 (by decide)
  have h9 : Entails.eval a c218 := h 217 (by decide)
  have h10 : Entails.eval a c521 := derived521 a h
  have h11 : Entails.eval a c203 := h 202 (by decide)
  have h12 : Entails.eval a c150 := h 149 (by decide)
  have h13 : Entails.eval a c209 := h 208 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1163 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨14, by decide⟩, true), (⟨8, by decide⟩, true), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c71, some c166, some c354, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 57) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c71, c166, c354] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c166 := h 165 (by decide)
  have h2 : Entails.eval a c354 := h 353 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1164 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1037, some c146, some c154, some c354, some c213, some c24, some c134, some c270, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 57) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c1037, c146, c154, c354, c213, c24, c134, c270] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c1037 := derived1037 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c354 := h 353 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 57 := directClause [(⟨26, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true), (⟨14, by decide⟩, true), (⟨15, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1162, some c32, some c268, some c269, some c134, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 57) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c1162, c32, c268, c269, c134] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c1162 := derived1162 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨15, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨36, by decide⟩, false), (⟨18, by decide⟩, false), (⟨23, by decide⟩, true), (⟨11, by decide⟩, true), (⟨33, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1077, some c1163, some c359, some c1164, some c1165, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 57) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c1077, c1163, c359, c1164, c1165] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c1077 := derived1077 a h
  have h1 : Entails.eval a c1163 := derived1163 a h
  have h2 : Entails.eval a c359 := h 358 (by decide)
  have h3 : Entails.eval a c1164 := derived1164 a h
  have h4 : Entails.eval a c1165 := derived1165 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨26, by decide⟩, false), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c24, some c44, some c216, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 57) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c24, c44, c216] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c216 := h 215 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c269, some c270, some c33, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p1168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 57) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c269, c270, c33] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c269 := h 268 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨26, by decide⟩, true), (⟨36, by decide⟩, true), (⟨3, by decide⟩, false), (⟨24, by decide⟩, true), (⟨22, by decide⟩, true), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c24, some c1077, some c358, some c906, some c118, some c109, some c40, some c33, some c236, some c72, some c112, some c35, some c265, some c220, some c631, some c152, some c49, some c2, some c185, some c260, some c95, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 57) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c110, c24, c1077, c358, c906, c118, c109, c40, c33, c236, c72, c112, c35, c265, c220, c631, c152, c49, c2, c185, c260, c95] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c1077 := derived1077 a h
  have h3 : Entails.eval a c358 := h 357 (by decide)
  have h4 : Entails.eval a c906 := derived906 a h
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c236 := h 235 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c112 := h 111 (by decide)
  have h12 : Entails.eval a c35 := h 34 (by decide)
  have h13 : Entails.eval a c265 := h 264 (by decide)
  have h14 : Entails.eval a c220 := h 219 (by decide)
  have h15 : Entails.eval a c631 := derived631 a h
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c49 := h 48 (by decide)
  have h18 : Entails.eval a c2 := h 1 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c260 := h 259 (by decide)
  have h21 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c1168, some c24, some c33, some c268, some c31, some c1077, some c612, some c358, some c40, some c230, some c118, some c906, some c214, some c1169, some c355, some c360, some c67, some c234, some c2, some c220, some c149, some c163, some c145, some c282, some c207, some c314, some c123, some c52, some c81, some c331, some c352, some c344, some c365, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 57) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c109, c110, c1168, c24, c33, c268, c31, c1077, c612, c358, c40, c230, c118, c906, c214, c1169, c355, c360, c67, c234, c2, c220, c149, c163, c145, c282, c207, c314, c123, c52, c81, c331, c352, c344, c365] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c1168 := derived1168 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c1077 := derived1077 a h
  have h8 : Entails.eval a c612 := derived612 a h
  have h9 : Entails.eval a c358 := h 357 (by decide)
  have h10 : Entails.eval a c40 := h 39 (by decide)
  have h11 : Entails.eval a c230 := h 229 (by decide)
  have h12 : Entails.eval a c118 := h 117 (by decide)
  have h13 : Entails.eval a c906 := derived906 a h
  have h14 : Entails.eval a c214 := h 213 (by decide)
  have h15 : Entails.eval a c1169 := derived1169 a h
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c360 := h 359 (by decide)
  have h18 : Entails.eval a c67 := h 66 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c2 := h 1 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c149 := h 148 (by decide)
  have h23 : Entails.eval a c163 := h 162 (by decide)
  have h24 : Entails.eval a c145 := h 144 (by decide)
  have h25 : Entails.eval a c282 := h 281 (by decide)
  have h26 : Entails.eval a c207 := h 206 (by decide)
  have h27 : Entails.eval a c314 := h 313 (by decide)
  have h28 : Entails.eval a c123 := h 122 (by decide)
  have h29 : Entails.eval a c52 := h 51 (by decide)
  have h30 : Entails.eval a c81 := h 80 (by decide)
  have h31 : Entails.eval a c331 := h 330 (by decide)
  have h32 : Entails.eval a c352 := h 351 (by decide)
  have h33 : Entails.eval a c344 := h 343 (by decide)
  have h34 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨20, by decide⟩, false), (⟨39, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c1168, some c268, some c230, some c360, some c234, some c906, some c118, some c1170, some c612, some c73, some c40, some c355, some c214, some c220, some c67, some c41, some c145, some c2, some c971, some c149, some c163, some c212, some c207, some c52, some c123, some c352, some c256, some c325, some c331, some c365, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 57) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c109, c110, c1168, c268, c230, c360, c234, c906, c118, c1170, c612, c73, c40, c355, c214, c220, c67, c41, c145, c2, c971, c149, c163, c212, c207, c52, c123, c352, c256, c325, c331, c365] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c1168 := derived1168 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c230 := h 229 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c906 := derived906 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c1170 := derived1170 a h
  have h10 : Entails.eval a c612 := derived612 a h
  have h11 : Entails.eval a c73 := h 72 (by decide)
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c214 := h 213 (by decide)
  have h15 : Entails.eval a c220 := h 219 (by decide)
  have h16 : Entails.eval a c67 := h 66 (by decide)
  have h17 : Entails.eval a c41 := h 40 (by decide)
  have h18 : Entails.eval a c145 := h 144 (by decide)
  have h19 : Entails.eval a c2 := h 1 (by decide)
  have h20 : Entails.eval a c971 := derived971 a h
  have h21 : Entails.eval a c149 := h 148 (by decide)
  have h22 : Entails.eval a c163 := h 162 (by decide)
  have h23 : Entails.eval a c212 := h 211 (by decide)
  have h24 : Entails.eval a c207 := h 206 (by decide)
  have h25 : Entails.eval a c52 := h 51 (by decide)
  have h26 : Entails.eval a c123 := h 122 (by decide)
  have h27 : Entails.eval a c352 := h 351 (by decide)
  have h28 : Entails.eval a c256 := h 255 (by decide)
  have h29 : Entails.eval a c325 := h 324 (by decide)
  have h30 : Entails.eval a c331 := h 330 (by decide)
  have h31 : Entails.eval a c365 := h 364 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨20, by decide⟩, false), (⟨39, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1170, some c109, some c110, some c1168, some c906, some c1171, some c142, some c666, some c216, some c61, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 57) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c1170, c109, c110, c1168, c906, c1171, c142, c666, c216, c61] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c1170 := derived1170 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c1168 := derived1168 a h
  have h4 : Entails.eval a c906 := derived906 a h
  have h5 : Entails.eval a c1171 := derived1171 a h
  have h6 : Entails.eval a c142 := h 141 (by decide)
  have h7 : Entails.eval a c666 := derived666 a h
  have h8 : Entails.eval a c216 := h 215 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 57 := directClause [(⟨26, by decide⟩, false), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c214, some c216, some c61, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 57) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c214, c216, c61] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c214 := h 213 (by decide)
  have h1 : Entails.eval a c216 := h 215 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨31, by decide⟩, true), (⟨25, by decide⟩, false), (⟨12, by decide⟩, true), (⟨3, by decide⟩, true), (⟨19, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c60, some c156, some c212, some c1080, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 57) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c61, c60, c156, c212, c1080] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c60 := h 59 (by decide)
  have h2 : Entails.eval a c156 := h 155 (by decide)
  have h3 : Entails.eval a c212 := h 211 (by decide)
  have h4 : Entails.eval a c1080 := derived1080 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨20, by decide⟩, false), (⟨39, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c109, some c1170, some c1173, some c268, some c1168, some c1077, some c19, some c360, some c142, some c276, some c7, some c134, some c1149, some c1139, some c273, some c313, some c1174, some c220, some c319, some c117, some c21, some c59, some c971, some c212, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 57) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c110, c109, c1170, c1173, c268, c1168, c1077, c19, c360, c142, c276, c7, c134, c1149, c1139, c273, c313, c1174, c220, c319, c117, c21, c59, c971, c212] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c1170 := derived1170 a h
  have h3 : Entails.eval a c1173 := derived1173 a h
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c1168 := derived1168 a h
  have h6 : Entails.eval a c1077 := derived1077 a h
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c360 := h 359 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c276 := h 275 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c1149 := derived1149 a h
  have h14 : Entails.eval a c1139 := derived1139 a h
  have h15 : Entails.eval a c273 := h 272 (by decide)
  have h16 : Entails.eval a c313 := h 312 (by decide)
  have h17 : Entails.eval a c1174 := derived1174 a h
  have h18 : Entails.eval a c220 := h 219 (by decide)
  have h19 : Entails.eval a c319 := h 318 (by decide)
  have h20 : Entails.eval a c117 := h 116 (by decide)
  have h21 : Entails.eval a c21 := h 20 (by decide)
  have h22 : Entails.eval a c59 := h 58 (by decide)
  have h23 : Entails.eval a c971 := derived971 a h
  have h24 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨39, by decide⟩, false), (⟨18, by decide⟩, false), (⟨2, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c110, some c1168, some c268, some c1172, some c1175, some c612, some c358, some c73, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 57) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c109, c110, c1168, c268, c1172, c1175, c612, c358, c73] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c1168 := derived1168 a h
  have h3 : Entails.eval a c268 := h 267 (by decide)
  have h4 : Entails.eval a c1172 := derived1172 a h
  have h5 : Entails.eval a c1175 := derived1175 a h
  have h6 : Entails.eval a c612 := derived612 a h
  have h7 : Entails.eval a c358 := h 357 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨40, by decide⟩, true), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨19, by decide⟩, false), (⟨20, by decide⟩, true), (⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c44, some c143, some c278, some c314, some c274, some c149, some c353, some c1089, some c202, some c75, some c153, some c171, some c815, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 57) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c44, c143, c278, c314, c274, c149, c353, c1089, c202, c75, c153, c171, c815] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c44 := h 43 (by decide)
  have h1 : Entails.eval a c143 := h 142 (by decide)
  have h2 : Entails.eval a c278 := h 277 (by decide)
  have h3 : Entails.eval a c314 := h 313 (by decide)
  have h4 : Entails.eval a c274 := h 273 (by decide)
  have h5 : Entails.eval a c149 := h 148 (by decide)
  have h6 : Entails.eval a c353 := h 352 (by decide)
  have h7 : Entails.eval a c1089 := derived1089 a h
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c75 := h 74 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c171 := h 170 (by decide)
  have h12 : Entails.eval a c815 := derived815 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 57 := directClause [(⟨37, by decide⟩, true), (⟨40, by decide⟩, true), (⟨34, by decide⟩, false), (⟨20, by decide⟩, true), (⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c356, some c71, some c357, some c612, some c234, some c75, some c272, some c112, some c32, some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 57) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c20, c356, c71, c357, c612, c234, c75, c272, c112, c32] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c357 := h 356 (by decide)
  have h4 : Entails.eval a c612 := derived612 a h
  have h5 : Entails.eval a c234 := h 233 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c272 := h 271 (by decide)
  have h8 : Entails.eval a c112 := h 111 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, false), (⟨33, by decide⟩, true), (⟨3, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c971, some c112, some c267, some c32, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p1179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 57) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c971, c112, c267, c32] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c971 := derived971 a h
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c267 := h 266 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨49, by decide⟩, false), (⟨33, by decide⟩, true), (⟨37, by decide⟩, false), (⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨10, by decide⟩, true), (⟨20, by decide⟩, true), (⟨24, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c152, some c1179, some c49, some c348, some c185, some c101, some c631, some c252, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 57) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c20, c152, c1179, c49, c348, c185, c101, c631, c252] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c1179 := derived1179 a h
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c348 := h 347 (by decide)
  have h5 : Entails.eval a c185 := h 184 (by decide)
  have h6 : Entails.eval a c101 := h 100 (by decide)
  have h7 : Entails.eval a c631 := derived631 a h
  have h8 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨10, by decide⟩, true), (⟨34, by decide⟩, false), (⟨20, by decide⟩, true), (⟨39, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1168, some c20, some c357, some c118, some c356, some c612, some c71, some c44, some c1167, some c1177, some c1178, some c353, some c452, some c1180, some c320, some c319, some c153, some c48, some c60, some c342, some c11, some c305, some c162, some c187, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 57) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c1168, c20, c357, c118, c356, c612, c71, c44, c1167, c1177, c1178, c353, c452, c1180, c320, c319, c153, c48, c60, c342, c11, c305, c162, c187] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c1168 := derived1168 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c612 := derived612 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c1167 := derived1167 a h
  have h9 : Entails.eval a c1177 := derived1177 a h
  have h10 : Entails.eval a c1178 := derived1178 a h
  have h11 : Entails.eval a c353 := h 352 (by decide)
  have h12 : Entails.eval a c452 := derived452 a h
  have h13 : Entails.eval a c1180 := derived1180 a h
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  have h16 : Entails.eval a c153 := h 152 (by decide)
  have h17 : Entails.eval a c48 := h 47 (by decide)
  have h18 : Entails.eval a c60 := h 59 (by decide)
  have h19 : Entails.eval a c342 := h 341 (by decide)
  have h20 : Entails.eval a c11 := h 10 (by decide)
  have h21 : Entails.eval a c305 := h 304 (by decide)
  have h22 : Entails.eval a c162 := h 161 (by decide)
  have h23 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 57 := directClause [(⟨31, by decide⟩, true), (⟨53, by decide⟩, true), (⟨50, by decide⟩, true), (⟨28, by decide⟩, true), (⟨26, by decide⟩, true), (⟨3, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c305, some c112, some c352, some c103, some (DefaultClause.unit (⟨31, by decide⟩, false)), some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 57) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c60, c305, c112, c352, c103] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c305 := h 304 (by decide)
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c352 := h 351 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨29, by decide⟩, false), (⟨33, by decide⟩, true), (⟨35, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c320, some c313, some c274, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false))]
def p1183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 57) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c320, c313, c274] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c320 := h 319 (by decide)
  have h1 : Entails.eval a c313 := h 312 (by decide)
  have h2 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived1183

end CochromaticTwenty.Certificates.B16_4_2
