import MerLeanExperiment.Certificates.Z12Direct_5_8_7.Steps0300_0399

/-! Generated from the actual pinned z12direct_5_8_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1145 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1143, some c1140, some c1144, some c53, some c114, some c1129, some c1108, some c1055, some c51, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1145 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 31) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1143, c1140, c1144, c53, c114, c1129, c1108, c1055, c51] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1143 := derived1143 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c1129 := derived1129 a h
  have h6 : Entails.eval a c1108 := derived1108 a h
  have h7 : Entails.eval a c1055 := derived1055 a h
  have h8 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c1145, some c256, some c10, some c287, some c53, some c266, some c1033, some c30, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1146 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 31) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1140, c1145, c256, c10, c287, c53, c266, c1033, c30] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1145 := derived1145 a h
  have h2 : Entails.eval a c256 := h 255 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c287 := h 286 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c266 := h 265 (by decide)
  have h7 : Entails.eval a c1033 := derived1033 a h
  have h8 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1146, some c1143, some c1140, some c29, some c256, some c287, some c214, some c1042, some c1035, some c634, some c240, some c1055, some c1108, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1147 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 31) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c1146, c1143, c1140, c29, c256, c287, c214, c1042, c1035, c634, c240, c1055, c1108] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c1146 := derived1146 a h
  have h1 : Entails.eval a c1143 := derived1143 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c256 := h 255 (by decide)
  have h5 : Entails.eval a c287 := h 286 (by decide)
  have h6 : Entails.eval a c214 := h 213 (by decide)
  have h7 : Entails.eval a c1042 := derived1042 a h
  have h8 : Entails.eval a c1035 := derived1035 a h
  have h9 : Entails.eval a c634 := h 633 (by decide)
  have h10 : Entails.eval a c240 := h 239 (by decide)
  have h11 : Entails.eval a c1055 := derived1055 a h
  have h12 : Entails.eval a c1108 := derived1108 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1147, some c1146, some c1143, some c1140, some c53, some c54, some c87, some c1093, some c511, some c31, some c51, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1148 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 31) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c1147, c1146, c1143, c1140, c53, c54, c87, c1093, c511, c31, c51] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1146 := derived1146 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c1093 := derived1093 a h
  have h8 : Entails.eval a c511 := h 510 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨19, by decide⟩, false), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, true), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c31, some c1117, some c274, some c240, some c16, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1149 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 31) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c31, c1117, c274, c240, c16] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c1117 := derived1117 a h
  have h2 : Entails.eval a c274 := h 273 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c1141, some c1143, some c1146, some c1147, some c1148, some c1149, some c602, some c496, some c51, some c1129, some c744, some c607, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1150 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 31) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1140, c1141, c1143, c1146, c1147, c1148, c1149, c602, c496, c51, c1129, c744, c607] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1141 := derived1141 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1146 := derived1146 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c1148 := derived1148 a h
  have h6 : Entails.eval a c1149 := derived1149 a h
  have h7 : Entails.eval a c602 := h 601 (by decide)
  have h8 : Entails.eval a c496 := h 495 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c1129 := derived1129 a h
  have h11 : Entails.eval a c744 := h 743 (by decide)
  have h12 : Entails.eval a c607 := h 606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1129, some c988, some c744, some c607, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 31) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1129, c988, c744, c607] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1129 := derived1129 a h
  have h1 : Entails.eval a c988 := derived988 a h
  have h2 : Entails.eval a c744 := h 743 (by decide)
  have h3 : Entails.eval a c607 := h 606 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1150, some c1140, some c1143, some c1146, some c1147, some c1148, some c1151, some c51, some c1087, some c543, some c36, some c293, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1152 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 31) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c1150, c1140, c1143, c1146, c1147, c1148, c1151, c51, c1087, c543, c36, c293] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c1150 := derived1150 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1143 := derived1143 a h
  have h3 : Entails.eval a c1146 := derived1146 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c1148 := derived1148 a h
  have h6 : Entails.eval a c1151 := derived1151 a h
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c1087 := derived1087 a h
  have h9 : Entails.eval a c543 := h 542 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c1150, some c1152, some c238, some c76, some c1031, some c31, some c34, some c59, some c54, some c37, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1153 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 31) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1140, c1150, c1152, c238, c76, c1031, c31, c34, c59, c54, c37] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1150 := derived1150 a h
  have h2 : Entails.eval a c1152 := derived1152 a h
  have h3 : Entails.eval a c238 := h 237 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c1031 := derived1031 a h
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1153, some c1140, some c1115, some c1121, some c1080, some c1050, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1154 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 31) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c1153, c1140, c1115, c1121, c1080, c1050] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1115 := derived1115 a h
  have h3 : Entails.eval a c1121 := derived1121 a h
  have h4 : Entails.eval a c1080 := derived1080 a h
  have h5 : Entails.eval a c1050 := derived1050 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨7, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c38, some c51, some c1153, some c1140, some c240, some c156, some c15, some c952, some c3, some c293, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1155 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 31) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c38, c51, c1153, c1140, c240, c156, c15, c952, c3, c293] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c1153 := derived1153 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c240 := h 239 (by decide)
  have h5 : Entails.eval a c156 := h 155 (by decide)
  have h6 : Entails.eval a c15 := h 14 (by decide)
  have h7 : Entails.eval a c952 := derived952 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨4, by decide⟩, false), (⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1020, some c1070, some c600, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p1156 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 31) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c1020, c1070, c600] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c1020 := derived1020 a h
  have h1 : Entails.eval a c1070 := derived1070 a h
  have h2 : Entails.eval a c600 := h 599 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1154, some c1153, some c1140, some c51, some c34, some c1156, some c156, some c1155, some c653, some c624, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1157 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 31) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c1154, c1153, c1140, c51, c34, c1156, c156, c1155, c653, c624] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c1154 := derived1154 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c1156 := derived1156 a h
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c1155 := derived1155 a h
  have h8 : Entails.eval a c653 := h 652 (by decide)
  have h9 : Entails.eval a c624 := h 623 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨16, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c54, some c1093, some c1108, some c134, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1158 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 31) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c1140, c54, c1093, c1108, c134] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c1093 := derived1093 a h
  have h3 : Entails.eval a c1108 := derived1108 a h
  have h4 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1102, some c1103, some c1104, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1159 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 31) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c1102, c1103, c1104] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c1102 := derived1102 a h
  have h1 : Entails.eval a c1103 := derived1103 a h
  have h2 : Entails.eval a c1104 := derived1104 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1153, some c1140, some c1154, some c1157, some c31, some c1158, some c1159, some c421, some c240, some c1041, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1160 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 31) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c1153, c1140, c1154, c1157, c31, c1158, c1159, c421, c240, c1041] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1154 := derived1154 a h
  have h3 : Entails.eval a c1157 := derived1157 a h
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c1158 := derived1158 a h
  have h6 : Entails.eval a c1159 := derived1159 a h
  have h7 : Entails.eval a c421 := h 420 (by decide)
  have h8 : Entails.eval a c240 := h 239 (by decide)
  have h9 : Entails.eval a c1041 := derived1041 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c1159, some c298, some c31, some c1153, some c14, some c1041, some c723, some c3, some c421, some c1038, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1161 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 31) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c1140, c1159, c298, c31, c1153, c14, c1041, c723, c3, c421, c1038] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1159 := derived1159 a h
  have h2 : Entails.eval a c298 := h 297 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c1153 := derived1153 a h
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c1041 := derived1041 a h
  have h7 : Entails.eval a c723 := h 722 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c421 := h 420 (by decide)
  have h10 : Entails.eval a c1038 := derived1038 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c31, some c1159, some c1158, some c1161, some c1050, some c240, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1162 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 31) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c1140, c31, c1159, c1158, c1161, c1050, c240] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1159 := derived1159 a h
  have h3 : Entails.eval a c1158 := derived1158 a h
  have h4 : Entails.eval a c1161 := derived1161 a h
  have h5 : Entails.eval a c1050 := derived1050 a h
  have h6 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1163 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1162, some c1160, some c1153, some c1140, some c51, some c274, some c156, some c624, some c514, some c47, some c284, some c208, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1163 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 31) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c1162, c1160, c1153, c1140, c51, c274, c156, c624, c514, c47, c284, c208] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c1162 := derived1162 a h
  have h1 : Entails.eval a c1160 := derived1160 a h
  have h2 : Entails.eval a c1153 := derived1153 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c274 := h 273 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c624 := h 623 (by decide)
  have h8 : Entails.eval a c514 := h 513 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c284 := h 283 (by decide)
  have h11 : Entails.eval a c208 := h 207 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1164 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1153, some c1140, some c1163, some c1115, some c1050, some c1121, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1164 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 31) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c1153, c1140, c1163, c1115, c1050, c1121] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1163 := derived1163 a h
  have h3 : Entails.eval a c1115 := derived1115 a h
  have h4 : Entails.eval a c1050 := derived1050 a h
  have h5 : Entails.eval a c1121 := derived1121 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨27, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c255, some c208, some c284, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1165 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 31) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c255, c208, c284] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c255 := h 254 (by decide)
  have h1 : Entails.eval a c208 := h 207 (by decide)
  have h2 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1153, some c1140, some c1160, some c1162, some c1164, some c1041, some c1165, some c14, some c1115, some c274, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1166 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 31) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c1153, c1140, c1160, c1162, c1164, c1041, c1165, c14, c1115, c274] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1160 := derived1160 a h
  have h3 : Entails.eval a c1162 := derived1162 a h
  have h4 : Entails.eval a c1164 := derived1164 a h
  have h5 : Entails.eval a c1041 := derived1041 a h
  have h6 : Entails.eval a c1165 := derived1165 a h
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c1115 := derived1115 a h
  have h9 : Entails.eval a c274 := h 273 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1153, some c1140, some c106, some c430, some c80, some c1114, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1167 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 31) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c1166, c1153, c1140, c106, c430, c80, c1114] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c430 := h 429 (by decide)
  have h5 : Entails.eval a c80 := h 79 (by decide)
  have h6 : Entails.eval a c1114 := derived1114 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1153, some c1072, some c1140, some c1167, some c1127, some c1033, some c51, some c258, some c1093, some c511, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1168 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 31) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c1166, c1153, c1072, c1140, c1167, c1127, c1033, c51, c258, c1093, c511] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1072 := derived1072 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c1167 := derived1167 a h
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c1033 := derived1033 a h
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c258 := h 257 (by decide)
  have h9 : Entails.eval a c1093 := derived1093 a h
  have h10 : Entails.eval a c511 := h 510 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1153, some c1168, some c29, some c9, some c255, some c1165, some c1036, some c376, some c412, some c391, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1169 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 31) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c1166, c1153, c1168, c29, c9, c255, c1165, c1036, c376, c412, c391] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1168 := derived1168 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c255 := h 254 (by decide)
  have h6 : Entails.eval a c1165 := derived1165 a h
  have h7 : Entails.eval a c1036 := derived1036 a h
  have h8 : Entails.eval a c376 := h 375 (by decide)
  have h9 : Entails.eval a c412 := h 411 (by decide)
  have h10 : Entails.eval a c391 := h 390 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1169, some c1166, some c1153, some c1140, some c29, some c9, some c255, some c1165, some c284, some c1039, some c486, some c265, some c399, some c732, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1170 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 31) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c1169, c1166, c1153, c1140, c29, c9, c255, c1165, c284, c1039, c486, c265, c399, c732] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c1169 := derived1169 a h
  have h1 : Entails.eval a c1166 := derived1166 a h
  have h2 : Entails.eval a c1153 := derived1153 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c255 := h 254 (by decide)
  have h7 : Entails.eval a c1165 := derived1165 a h
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c1039 := derived1039 a h
  have h10 : Entails.eval a c486 := h 485 (by decide)
  have h11 : Entails.eval a c265 := h 264 (by decide)
  have h12 : Entails.eval a c399 := h 398 (by decide)
  have h13 : Entails.eval a c732 := h 731 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨27, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c1033, some c1093, some c1153, some c186, some c449, some c691, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1171 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 31) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c1140, c1033, c1093, c1153, c186, c449, c691] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1033 := derived1033 a h
  have h2 : Entails.eval a c1093 := derived1093 a h
  have h3 : Entails.eval a c1153 := derived1153 a h
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c449 := h 448 (by decide)
  have h6 : Entails.eval a c691 := h 690 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1170, some c1169, some c1166, some c1153, some c1140, some c1127, some c1033, some c1171, some c1107, some c51, some c156, some c525, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1172 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 31) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c1170, c1169, c1166, c1153, c1140, c1127, c1033, c1171, c1107, c51, c156, c525] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c1170 := derived1170 a h
  have h1 : Entails.eval a c1169 := derived1169 a h
  have h2 : Entails.eval a c1166 := derived1166 a h
  have h3 : Entails.eval a c1153 := derived1153 a h
  have h4 : Entails.eval a c1140 := derived1140 a h
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c1033 := derived1033 a h
  have h7 : Entails.eval a c1171 := derived1171 a h
  have h8 : Entails.eval a c1107 := derived1107 a h
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  have h11 : Entails.eval a c525 := h 524 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1153, some c1140, some c1166, some c1170, some c1172, some c181, some c1167, some c185, some c1128, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1173 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 31) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c1153, c1140, c1166, c1170, c1172, c181, c1167, c185, c1128] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c1153 := derived1153 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1166 := derived1166 a h
  have h3 : Entails.eval a c1170 := derived1170 a h
  have h4 : Entails.eval a c1172 := derived1172 a h
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c1167 := derived1167 a h
  have h7 : Entails.eval a c185 := h 184 (by decide)
  have h8 : Entails.eval a c1128 := derived1128 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1173, some c1153, some c1140, some c185, some c1035, some c53, some c1128, some c1033, some c240, some c729, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1174 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 31) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c1173, c1153, c1140, c185, c1035, c53, c1128, c1033, c240, c729] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c185 := h 184 (by decide)
  have h4 : Entails.eval a c1035 := derived1035 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c1128 := derived1128 a h
  have h7 : Entails.eval a c1033 := derived1033 a h
  have h8 : Entails.eval a c240 := h 239 (by decide)
  have h9 : Entails.eval a c729 := h 728 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1173, some c1153, some c1140, some c1174, some c181, some c1127, some c1033, some c1171, some c53, some c10, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1175 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 31) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c1173, c1153, c1140, c1174, c181, c1127, c1033, c1171, c53, c10] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1174 := derived1174 a h
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c1033 := derived1033 a h
  have h7 : Entails.eval a c1171 := derived1171 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨16, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1175, some c9, some c29, some c1173, some c1153, some c1140, some c1036, some c1171, some c997, some c298, some c689, some c1129, some c1092, some c550, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1176 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 31) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c1175, c9, c29, c1173, c1153, c1140, c1036, c1171, c997, c298, c689, c1129, c1092, c550] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c1175 := derived1175 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c1173 := derived1173 a h
  have h4 : Entails.eval a c1153 := derived1153 a h
  have h5 : Entails.eval a c1140 := derived1140 a h
  have h6 : Entails.eval a c1036 := derived1036 a h
  have h7 : Entails.eval a c1171 := derived1171 a h
  have h8 : Entails.eval a c997 := derived997 a h
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c689 := h 688 (by decide)
  have h11 : Entails.eval a c1129 := derived1129 a h
  have h12 : Entails.eval a c1092 := derived1092 a h
  have h13 : Entails.eval a c550 := h 549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1173, some c1140, some c1175, some c29, some c1176, some c181, some c208, some c1129, some c53, some c1033, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1177 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 31) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c1173, c1140, c1175, c29, c1176, c181, c208, c1129, c53, c1033] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c1173 := derived1173 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1175 := derived1175 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c1176 := derived1176 a h
  have h5 : Entails.eval a c181 := h 180 (by decide)
  have h6 : Entails.eval a c208 := h 207 (by decide)
  have h7 : Entails.eval a c1129 := derived1129 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c1033 := derived1033 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1173, some c1140, some c1100, some c1067, some c51, some c274, some c1087, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1178 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 31) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c1177, c1173, c1140, c1100, c1067, c51, c274, c1087] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1173 := derived1173 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c1067 := derived1067 a h
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c1087 := derived1087 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨26, by decide⟩, true), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1173, some c1153, some c1140, some c1178, some c29, some c1115, some c688, some c678, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1179 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 31) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c1177, c1173, c1153, c1140, c1178, c29, c1115, c688, c678] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1173 := derived1173 a h
  have h2 : Entails.eval a c1153 := derived1153 a h
  have h3 : Entails.eval a c1140 := derived1140 a h
  have h4 : Entails.eval a c1178 := derived1178 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c1115 := derived1115 a h
  have h7 : Entails.eval a c688 := h 687 (by decide)
  have h8 : Entails.eval a c678 := h 677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1173, some c1140, some c1042, some c1179, some c31, some c1158, some c474, some c1054, some c30, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1180 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 31) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c1177, c1173, c1140, c1042, c1179, c31, c1158, c474, c1054, c30] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1173 := derived1173 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1042 := derived1042 a h
  have h4 : Entails.eval a c1179 := derived1179 a h
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c1158 := derived1158 a h
  have h7 : Entails.eval a c474 := h 473 (by decide)
  have h8 : Entails.eval a c1054 := derived1054 a h
  have h9 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1140, some c1180, some c78, some c82, some c134, some c31, some c1040, some c51, some c34, some c49, some c274, some c156, some c245, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1181 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 31) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c1177, c1140, c1180, c78, c82, c134, c31, c1040, c51, c34, c49, c274, c156, c245] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c1180 := derived1180 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c1040 := derived1040 a h
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c274 := h 273 (by decide)
  have h12 : Entails.eval a c156 := h 155 (by decide)
  have h13 : Entails.eval a c245 := h 244 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1153, some c1140, some c1181, some c1041, some c1173, some c51, some c156, some c496, some c624, some c29, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1182 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 31) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c1177, c1153, c1140, c1181, c1041, c1173, c51, c156, c496, c624, c29] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1181 := derived1181 a h
  have h4 : Entails.eval a c1041 := derived1041 a h
  have h5 : Entails.eval a c1173 := derived1173 a h
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c156 := h 155 (by decide)
  have h8 : Entails.eval a c496 := h 495 (by decide)
  have h9 : Entails.eval a c624 := h 623 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1177, some c1153, some c1140, some c1181, some c1041, some c1115, some c1050, some c1121, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1183 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 31) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1177, c1153, c1140, c1181, c1041, c1115, c1050, c1121] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1177 := derived1177 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1140 := derived1140 a h
  have h3 : Entails.eval a c1181 := derived1181 a h
  have h4 : Entails.eval a c1041 := derived1041 a h
  have h5 : Entails.eval a c1115 := derived1115 a h
  have h6 : Entails.eval a c1050 := derived1050 a h
  have h7 : Entails.eval a c1121 := derived1121 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1184 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1140, some c1153, some c1177, some c1181, some c1041, some c1183, some c1182, some c31, some c1127, some c1158, some c29, some c75, some c689, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1184 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 31) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1140, c1153, c1177, c1181, c1041, c1183, c1182, c31, c1127, c1158, c29, c75, c689] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c1177 := derived1177 a h
  have h3 : Entails.eval a c1181 := derived1181 a h
  have h4 : Entails.eval a c1041 := derived1041 a h
  have h5 : Entails.eval a c1183 := derived1183 a h
  have h6 : Entails.eval a c1182 := derived1182 a h
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c1127 := derived1127 a h
  have h9 : Entails.eval a c1158 := derived1158 a h
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c75 := h 74 (by decide)
  have h12 : Entails.eval a c689 := h 688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c31, some c240, some c75, some c1159, some c19, some c17, some c254, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1185 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 31) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c1184, c31, c240, c75, c1159, c19, c17, c254] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  have h4 : Entails.eval a c1159 := derived1159 a h
  have h5 : Entails.eval a c19 := h 18 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, true), (⟨22, by decide⟩, false), (⟨19, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1129, some c1099, some c466, some c542, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1186 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 31) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c1129, c1099, c466, c542] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c1129 := derived1129 a h
  have h1 : Entails.eval a c1099 := derived1099 a h
  have h2 : Entails.eval a c466 := h 465 (by decide)
  have h3 : Entails.eval a c542 := h 541 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c31, some c1185, some c54, some c254, some c1186, some c1159, some c41, some c421, some c298, some c529, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1187 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 31) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c1184, c31, c1185, c54, c254, c1186, c1159, c41, c421, c298, c529] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c1185 := derived1185 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c254 := h 253 (by decide)
  have h5 : Entails.eval a c1186 := derived1186 a h
  have h6 : Entails.eval a c1159 := derived1159 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c421 := h 420 (by decide)
  have h9 : Entails.eval a c298 := h 297 (by decide)
  have h10 : Entails.eval a c529 := h 528 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c76, some c1159, some c1127, some c421, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1188 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 31) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c76, c1159, c1127, c421] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c1159 := derived1159 a h
  have h2 : Entails.eval a c1127 := derived1127 a h
  have h3 : Entails.eval a c421 := h 420 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨10, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c54, some c656, some c1065, some c134, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1189 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 31) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c1184, c54, c656, c1065, c134] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c656 := h 655 (by decide)
  have h3 : Entails.eval a c1065 := derived1065 a h
  have h4 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨2, by decide⟩, true), (⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c31, some c54, some c1188, some c53, some c1186, some c272, some c1189, some c298, some c1037, some c592, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1190 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 31) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c1184, c31, c54, c1188, c53, c1186, c272, c1189, c298, c1037, c592] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c31 := h 30 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c1188 := derived1188 a h
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c1186 := derived1186 a h
  have h6 : Entails.eval a c272 := h 271 (by decide)
  have h7 : Entails.eval a c1189 := derived1189 a h
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c1037 := derived1037 a h
  have h10 : Entails.eval a c592 := h 591 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨16, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1187, some c1190, some c240, some c75, some c1035, some c1037, some c568, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1191 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 31) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c1184, c1187, c1190, c240, c75, c1035, c1037, c568] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1187 := derived1187 a h
  have h2 : Entails.eval a c1190 := derived1190 a h
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c1035 := derived1035 a h
  have h6 : Entails.eval a c1037 := derived1037 a h
  have h7 : Entails.eval a c568 := h 567 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1191, some c1050, some c54, some c31, some c1115, some c40, some c1116, some c1189, some c298, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1192 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 31) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c1191, c1050, c54, c31, c1115, c40, c1116, c1189, c298] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c1191 := derived1191 a h
  have h1 : Entails.eval a c1050 := derived1050 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c1115 := derived1115 a h
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c1116 := derived1116 a h
  have h7 : Entails.eval a c1189 := derived1189 a h
  have h8 : Entails.eval a c298 := h 297 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨7, by decide⟩, true), (⟨16, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1191, some c1050, some c54, some c1192, some c1132, some c1100, some c1159, some c236, some c298, some c291, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1193 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 31) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c1191, c1050, c54, c1192, c1132, c1100, c1159, c236, c298, c291] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c1191 := derived1191 a h
  have h1 : Entails.eval a c1050 := derived1050 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c1192 := derived1192 a h
  have h4 : Entails.eval a c1132 := derived1132 a h
  have h5 : Entails.eval a c1100 := derived1100 a h
  have h6 : Entails.eval a c1159 := derived1159 a h
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c298 := h 297 (by decide)
  have h9 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1194 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1193, some c512, some c1042, some c627, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1194 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 31) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c1184, c1193, c512, c1042, c627] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c512 := h 511 (by decide)
  have h3 : Entails.eval a c1042 := derived1042 a h
  have h4 : Entails.eval a c627 := h 626 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1195 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1193, some c18, some c1194, some c76, some c526, some c1041, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1195 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 31) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c1184, c1193, c18, c1194, c76, c526, c1041] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c18 := h 17 (by decide)
  have h3 : Entails.eval a c1194 := derived1194 a h
  have h4 : Entails.eval a c76 := h 75 (by decide)
  have h5 : Entails.eval a c526 := h 525 (by decide)
  have h6 : Entails.eval a c1041 := derived1041 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1193, some c1195, some c298, some c1159, some c1037, some c1042, some c78, some c594, some c1041, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1196 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 31) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c1184, c1193, c1195, c298, c1159, c1037, c1042, c78, c594, c1041] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c1195 := derived1195 a h
  have h3 : Entails.eval a c298 := h 297 (by decide)
  have h4 : Entails.eval a c1159 := derived1159 a h
  have h5 : Entails.eval a c1037 := derived1037 a h
  have h6 : Entails.eval a c1042 := derived1042 a h
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c594 := h 593 (by decide)
  have h9 : Entails.eval a c1041 := derived1041 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1196, some c1042, some c157, some c81, some c1100, some c180, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1197 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 31) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c1196, c1042, c157, c81, c1100, c180] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1042 := derived1042 a h
  have h2 : Entails.eval a c157 := h 156 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c1100 := derived1100 a h
  have h5 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1198 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨21, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1037, some c78, some c81, some c1036, some c180, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1198 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 31) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c1184, c1037, c78, c81, c1036, c180] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1037 := derived1037 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c1036 := derived1036 a h
  have h5 : Entails.eval a c180 := h 179 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1199 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨23, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c54, some c19, some c75, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1199 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 31) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c1184, c54, c19, c75] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨22, by decide⟩, false), (⟨2, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c254, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 31) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c282, c254] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c282 := h 281 (by decide)
  have h1 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1201 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1037, some c1196, some c1197, some c1198, some c1035, some c1199, some c1200, some c1100, some c223, some c156, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 31) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c1184, c1037, c1196, c1197, c1198, c1035, c1199, c1200, c1100, c223, c156] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1037 := derived1037 a h
  have h2 : Entails.eval a c1196 := derived1196 a h
  have h3 : Entails.eval a c1197 := derived1197 a h
  have h4 : Entails.eval a c1198 := derived1198 a h
  have h5 : Entails.eval a c1035 := derived1035 a h
  have h6 : Entails.eval a c1199 := derived1199 a h
  have h7 : Entails.eval a c1200 := derived1200 a h
  have h8 : Entails.eval a c1100 := derived1100 a h
  have h9 : Entails.eval a c223 := h 222 (by decide)
  have h10 : Entails.eval a c156 := h 155 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨5, by decide⟩, false), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1201, some c1037, some c1196, some c480, some c73, some c1079, some c1118, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 31) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c1184, c1201, c1037, c1196, c480, c73, c1079, c1118] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1201 := derived1201 a h
  have h2 : Entails.eval a c1037 := derived1037 a h
  have h3 : Entails.eval a c1196 := derived1196 a h
  have h4 : Entails.eval a c480 := h 479 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c1079 := derived1079 a h
  have h7 : Entails.eval a c1118 := derived1118 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1203 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1201, some c1103, some c1196, some c469, some c445, some c1039, some c38, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 31) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c1184, c1201, c1103, c1196, c469, c445, c1039, c38] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1201 := derived1201 a h
  have h2 : Entails.eval a c1103 := derived1103 a h
  have h3 : Entails.eval a c1196 := derived1196 a h
  have h4 : Entails.eval a c469 := h 468 (by decide)
  have h5 : Entails.eval a c445 := h 444 (by decide)
  have h6 : Entails.eval a c1039 := derived1039 a h
  have h7 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1204 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1196, some c1037, some c1201, some c1203, some c73, some c78, some c1202, some c1118, some c1199, some c629, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 31) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c1184, c1196, c1037, c1201, c1203, c73, c78, c1202, c1118, c1199, c629] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1196 := derived1196 a h
  have h2 : Entails.eval a c1037 := derived1037 a h
  have h3 : Entails.eval a c1201 := derived1201 a h
  have h4 : Entails.eval a c1203 := derived1203 a h
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c1202 := derived1202 a h
  have h8 : Entails.eval a c1118 := derived1118 a h
  have h9 : Entails.eval a c1199 := derived1199 a h
  have h10 : Entails.eval a c629 := h 628 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1205 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1204, some c54, some c18, some c1050, some c240, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 31) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c1184, c1204, c54, c18, c1050, c240] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c1050 := derived1050 a h
  have h5 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1206 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c156, some c240, some c26, some c420, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 31) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c1184, c156, c240, c26, c420] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c156 := h 155 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c420 := h 419 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1207 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c78, some c73, some c656, some c261, some c144, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 31) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c1184, c78, c73, c656, c261, c144] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c73 := h 72 (by decide)
  have h3 : Entails.eval a c656 := h 655 (by decide)
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1208 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1206, some c1050, some c1207, some c1040, some c451, some c576, some c52, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 31) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c1184, c1206, c1050, c1207, c1040, c451, c576, c52] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1206 := derived1206 a h
  have h2 : Entails.eval a c1050 := derived1050 a h
  have h3 : Entails.eval a c1207 := derived1207 a h
  have h4 : Entails.eval a c1040 := derived1040 a h
  have h5 : Entails.eval a c451 := h 450 (by decide)
  have h6 : Entails.eval a c576 := h 575 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1209 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨19, by decide⟩, true), (⟨12, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1040, some c451, some c576, some c52, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 31) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c1184, c1040, c451, c576, c52] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1040 := derived1040 a h
  have h2 : Entails.eval a c451 := h 450 (by decide)
  have h3 : Entails.eval a c576 := h 575 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1210 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1196, some c1204, some c1205, some c1208, some c73, some c1197, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 31) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c1196, c1204, c1205, c1208, c73, c1197] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  have h2 : Entails.eval a c1205 := derived1205 a h
  have h3 : Entails.eval a c1208 := derived1208 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c1197 := derived1197 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1211 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1204, some c1196, some c1205, some c1208, some c245, some c1210, some c1040, some c1209, some c134, some c527, some c1069, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 31) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c1184, c1204, c1196, c1205, c1208, c245, c1210, c1040, c1209, c134, c527, c1069] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  have h2 : Entails.eval a c1196 := derived1196 a h
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c1208 := derived1208 a h
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c1210 := derived1210 a h
  have h7 : Entails.eval a c1040 := derived1040 a h
  have h8 : Entails.eval a c1209 := derived1209 a h
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c527 := h 526 (by decide)
  have h11 : Entails.eval a c1069 := derived1069 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1212 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1204, some c1196, some c1211, some c28, some c264, some c234, some c13, some c1113, some c1073, some c1059, some c1061, some c616, some c272, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 31) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c1184, c1204, c1196, c1211, c28, c264, c234, c13, c1113, c1073, c1059, c1061, c616, c272] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  have h2 : Entails.eval a c1196 := derived1196 a h
  have h3 : Entails.eval a c1211 := derived1211 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c234 := h 233 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c1113 := derived1113 a h
  have h9 : Entails.eval a c1073 := derived1073 a h
  have h10 : Entails.eval a c1059 := derived1059 a h
  have h11 : Entails.eval a c1061 := derived1061 a h
  have h12 : Entails.eval a c616 := h 615 (by decide)
  have h13 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1213 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨10, by decide⟩, false), (⟨19, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c13, some c1073, some c1059, some c1061, some c616, some c272, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 31) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c1184, c13, c1073, c1059, c1061, c616, c272] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c1073 := derived1073 a h
  have h3 : Entails.eval a c1059 := derived1059 a h
  have h4 : Entails.eval a c1061 := derived1061 a h
  have h5 : Entails.eval a c616 := h 615 (by decide)
  have h6 : Entails.eval a c272 := h 271 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1214 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1212, some c1204, some c1196, some c28, some c264, some c13, some c1097, some c1213, some c356, some c1060, some c490, some c614, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1214 : lratChecker f1214 p1214 = .success := by decide +kernel
theorem unsat1214 : Unsatisfiable (PosFin 31) f1214 := by
  apply lratCheckerSound f1214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1214
  · intro a ha; simp [p1214] at ha; subst a; trivial
  · exact checked1214
theorem derived1214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1214 := by
  apply localUnsat_implies_entails f1214 [c1184, c1212, c1204, c1196, c28, c264, c13, c1097, c1213, c356, c1060, c490, c614] c1214 unsat1214 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1212 := derived1212 a h
  have h2 : Entails.eval a c1204 := derived1204 a h
  have h3 : Entails.eval a c1196 := derived1196 a h
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c1097 := derived1097 a h
  have h8 : Entails.eval a c1213 := derived1213 a h
  have h9 : Entails.eval a c356 := h 355 (by decide)
  have h10 : Entails.eval a c1060 := derived1060 a h
  have h11 : Entails.eval a c490 := h 489 (by decide)
  have h12 : Entails.eval a c614 := h 613 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1215 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1214, some c1205, some c1212, some c1065, some c1200, some c1196, some c1123, some c291, some c732, some c51, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1215 : lratChecker f1215 p1215 = .success := by decide +kernel
theorem unsat1215 : Unsatisfiable (PosFin 31) f1215 := by
  apply lratCheckerSound f1215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1215
  · intro a ha; simp [p1215] at ha; subst a; trivial
  · exact checked1215
theorem derived1215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1215 := by
  apply localUnsat_implies_entails f1215 [c1214, c1205, c1212, c1065, c1200, c1196, c1123, c291, c732, c51] c1215 unsat1215 (by rfl) a
  have h0 : Entails.eval a c1214 := derived1214 a h
  have h1 : Entails.eval a c1205 := derived1205 a h
  have h2 : Entails.eval a c1212 := derived1212 a h
  have h3 : Entails.eval a c1065 := derived1065 a h
  have h4 : Entails.eval a c1200 := derived1200 a h
  have h5 : Entails.eval a c1196 := derived1196 a h
  have h6 : Entails.eval a c1123 := derived1123 a h
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c732 := h 731 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1216 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1196, some c1204, some c1212, some c1214, some c1205, some c1065, some c1200, some c24, some c1215, some c510, some c448, some c201, some c130, some c184, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1216 : lratChecker f1216 p1216 = .success := by decide +kernel
theorem unsat1216 : Unsatisfiable (PosFin 31) f1216 := by
  apply lratCheckerSound f1216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1216
  · intro a ha; simp [p1216] at ha; subst a; trivial
  · exact checked1216
theorem derived1216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1216 := by
  apply localUnsat_implies_entails f1216 [c1196, c1204, c1212, c1214, c1205, c1065, c1200, c24, c1215, c510, c448, c201, c130, c184] c1216 unsat1216 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1204 := derived1204 a h
  have h2 : Entails.eval a c1212 := derived1212 a h
  have h3 : Entails.eval a c1214 := derived1214 a h
  have h4 : Entails.eval a c1205 := derived1205 a h
  have h5 : Entails.eval a c1065 := derived1065 a h
  have h6 : Entails.eval a c1200 := derived1200 a h
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c1215 := derived1215 a h
  have h9 : Entails.eval a c510 := h 509 (by decide)
  have h10 : Entails.eval a c448 := h 447 (by decide)
  have h11 : Entails.eval a c201 := h 200 (by decide)
  have h12 : Entails.eval a c130 := h 129 (by decide)
  have h13 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1217 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨7, by decide⟩, false), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1216, some c510, some c448, some c67, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1217 : lratChecker f1217 p1217 = .success := by decide +kernel
theorem unsat1217 : Unsatisfiable (PosFin 31) f1217 := by
  apply lratCheckerSound f1217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1217
  · intro a ha; simp [p1217] at ha; subst a; trivial
  · exact checked1217
theorem derived1217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1217 := by
  apply localUnsat_implies_entails f1217 [c1216, c510, c448, c67] c1217 unsat1217 (by rfl) a
  have h0 : Entails.eval a c1216 := derived1216 a h
  have h1 : Entails.eval a c510 := h 509 (by decide)
  have h2 : Entails.eval a c448 := h 447 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1218 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, false), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1068, some c67, some c1056, some c228, some c269, some c414, some c1039, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1218 : lratChecker f1218 p1218 = .success := by decide +kernel
theorem unsat1218 : Unsatisfiable (PosFin 31) f1218 := by
  apply lratCheckerSound f1218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1218
  · intro a ha; simp [p1218] at ha; subst a; trivial
  · exact checked1218
theorem derived1218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1218 := by
  apply localUnsat_implies_entails f1218 [c1184, c1216, c1068, c67, c1056, c228, c269, c414, c1039] c1218 unsat1218 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1068 := derived1068 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c1056 := derived1056 a h
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c414 := h 413 (by decide)
  have h8 : Entails.eval a c1039 := derived1039 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1219 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1068, some c1217, some c1218, some c1060, some c1048, some c1122, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1219 : lratChecker f1219 p1219 = .success := by decide +kernel
theorem unsat1219 : Unsatisfiable (PosFin 31) f1219 := by
  apply lratCheckerSound f1219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1219
  · intro a ha; simp [p1219] at ha; subst a; trivial
  · exact checked1219
theorem derived1219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1219 := by
  apply localUnsat_implies_entails f1219 [c1184, c1216, c1068, c1217, c1218, c1060, c1048, c1122] c1219 unsat1219 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1068 := derived1068 a h
  have h3 : Entails.eval a c1217 := derived1217 a h
  have h4 : Entails.eval a c1218 := derived1218 a h
  have h5 : Entails.eval a c1060 := derived1060 a h
  have h6 : Entails.eval a c1048 := derived1048 a h
  have h7 : Entails.eval a c1122 := derived1122 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1220 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1068, some c1060, some c1048, some c1058, some c1082, some c1086, some c270, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1220 : lratChecker f1220 p1220 = .success := by decide +kernel
theorem unsat1220 : Unsatisfiable (PosFin 31) f1220 := by
  apply lratCheckerSound f1220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1220
  · intro a ha; simp [p1220] at ha; subst a; trivial
  · exact checked1220
theorem derived1220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1220 := by
  apply localUnsat_implies_entails f1220 [c1184, c1216, c1068, c1060, c1048, c1058, c1082, c1086, c270] c1220 unsat1220 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1068 := derived1068 a h
  have h3 : Entails.eval a c1060 := derived1060 a h
  have h4 : Entails.eval a c1048 := derived1048 a h
  have h5 : Entails.eval a c1058 := derived1058 a h
  have h6 : Entails.eval a c1082 := derived1082 a h
  have h7 : Entails.eval a c1086 := derived1086 a h
  have h8 : Entails.eval a c270 := h 269 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1221 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1068, some c1219, some c1220, some c67, some c1218, some c295, some c228, some c1004, some c528, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1221 : lratChecker f1221 p1221 = .success := by decide +kernel
theorem unsat1221 : Unsatisfiable (PosFin 31) f1221 := by
  apply lratCheckerSound f1221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1221
  · intro a ha; simp [p1221] at ha; subst a; trivial
  · exact checked1221
theorem derived1221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1221 := by
  apply localUnsat_implies_entails f1221 [c1184, c1216, c1068, c1219, c1220, c67, c1218, c295, c228, c1004, c528] c1221 unsat1221 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1068 := derived1068 a h
  have h3 : Entails.eval a c1219 := derived1219 a h
  have h4 : Entails.eval a c1220 := derived1220 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c1218 := derived1218 a h
  have h7 : Entails.eval a c295 := h 294 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c1004 := derived1004 a h
  have h10 : Entails.eval a c528 := h 527 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1222 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c67, some c1056, some c1004, some c269, some c460, some c1095, some c1081, some c694, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1222 : lratChecker f1222 p1222 = .success := by decide +kernel
theorem unsat1222 : Unsatisfiable (PosFin 31) f1222 := by
  apply lratCheckerSound f1222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1222
  · intro a ha; simp [p1222] at ha; subst a; trivial
  · exact checked1222
theorem derived1222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1222 := by
  apply localUnsat_implies_entails f1222 [c1184, c1216, c67, c1056, c1004, c269, c460, c1095, c1081, c694] c1222 unsat1222 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c1056 := derived1056 a h
  have h4 : Entails.eval a c1004 := derived1004 a h
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c460 := h 459 (by decide)
  have h7 : Entails.eval a c1095 := derived1095 a h
  have h8 : Entails.eval a c1081 := derived1081 a h
  have h9 : Entails.eval a c694 := h 693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1223 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨1, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c405, some c694, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p1223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1223 : lratChecker f1223 p1223 = .success := by decide +kernel
theorem unsat1223 : Unsatisfiable (PosFin 31) f1223 := by
  apply lratCheckerSound f1223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1223
  · intro a ha; simp [p1223] at ha; subst a; trivial
  · exact checked1223
theorem derived1223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1223 := by
  apply localUnsat_implies_entails f1223 [c405, c694] c1223 unsat1223 (by rfl) a
  have h0 : Entails.eval a c405 := h 404 (by decide)
  have h1 : Entails.eval a c694 := h 693 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1224 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1223, some c270, some c281, some c407, some c737, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1224 : lratChecker f1224 p1224 = .success := by decide +kernel
theorem unsat1224 : Unsatisfiable (PosFin 31) f1224 := by
  apply lratCheckerSound f1224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1224
  · intro a ha; simp [p1224] at ha; subst a; trivial
  · exact checked1224
theorem derived1224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1224 := by
  apply localUnsat_implies_entails f1224 [c1223, c270, c281, c407, c737] c1224 unsat1224 (by rfl) a
  have h0 : Entails.eval a c1223 := derived1223 a h
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c281 := h 280 (by decide)
  have h3 : Entails.eval a c407 := h 406 (by decide)
  have h4 : Entails.eval a c737 := h 736 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1225 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1222, some c1216, some c1224, some c1059, some c460, some c517, some c71, some c78, some c82, some c86, some c339, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1225 : lratChecker f1225 p1225 = .success := by decide +kernel
theorem unsat1225 : Unsatisfiable (PosFin 31) f1225 := by
  apply lratCheckerSound f1225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1225
  · intro a ha; simp [p1225] at ha; subst a; trivial
  · exact checked1225
theorem derived1225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1225 := by
  apply localUnsat_implies_entails f1225 [c1184, c1222, c1216, c1224, c1059, c460, c517, c71, c78, c82, c86, c339] c1225 unsat1225 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1222 := derived1222 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c1224 := derived1224 a h
  have h4 : Entails.eval a c1059 := derived1059 a h
  have h5 : Entails.eval a c460 := h 459 (by decide)
  have h6 : Entails.eval a c517 := h 516 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c82 := h 81 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c339 := h 338 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1226 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨17, by decide⟩, true), (⟨3, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c16, some c1005, some c75, some c240, some c17, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1226 : lratChecker f1226 p1226 = .success := by decide +kernel
theorem unsat1226 : Unsatisfiable (PosFin 31) f1226 := by
  apply lratCheckerSound f1226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1226
  · intro a ha; simp [p1226] at ha; subst a; trivial
  · exact checked1226
theorem derived1226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1226 := by
  apply localUnsat_implies_entails f1226 [c16, c1005, c75, c240, c17] c1226 unsat1226 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c1005 := derived1005 a h
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1227 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1221, some c1216, some c1222, some c1226, some c1225, some c188, some c226, some c101, some c1078, some c1059, some c59, some c1109, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1227 : lratChecker f1227 p1227 = .success := by decide +kernel
theorem unsat1227 : Unsatisfiable (PosFin 31) f1227 := by
  apply lratCheckerSound f1227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1227
  · intro a ha; simp [p1227] at ha; subst a; trivial
  · exact checked1227
theorem derived1227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1227 := by
  apply localUnsat_implies_entails f1227 [c1184, c1221, c1216, c1222, c1226, c1225, c188, c226, c101, c1078, c1059, c59, c1109] c1227 unsat1227 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c1222 := derived1222 a h
  have h4 : Entails.eval a c1226 := derived1226 a h
  have h5 : Entails.eval a c1225 := derived1225 a h
  have h6 : Entails.eval a c188 := h 187 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  have h8 : Entails.eval a c101 := h 100 (by decide)
  have h9 : Entails.eval a c1078 := derived1078 a h
  have h10 : Entails.eval a c1059 := derived1059 a h
  have h11 : Entails.eval a c59 := h 58 (by decide)
  have h12 : Entails.eval a c1109 := derived1109 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1228 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1227, some c1221, some c1216, some c67, some c188, some c226, some c101, some c1078, some c59, some c254, some c573, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1228 : lratChecker f1228 p1228 = .success := by decide +kernel
theorem unsat1228 : Unsatisfiable (PosFin 31) f1228 := by
  apply lratCheckerSound f1228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1228
  · intro a ha; simp [p1228] at ha; subst a; trivial
  · exact checked1228
theorem derived1228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1228 := by
  apply localUnsat_implies_entails f1228 [c1184, c1227, c1221, c1216, c67, c188, c226, c101, c1078, c59, c254, c573] c1228 unsat1228 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1227 := derived1227 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c1216 := derived1216 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c188 := h 187 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c101 := h 100 (by decide)
  have h8 : Entails.eval a c1078 := derived1078 a h
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c254 := h 253 (by decide)
  have h11 : Entails.eval a c573 := h 572 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1229 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨17, by decide⟩, true), (⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1227, some c1221, some c59, some c750, some c1200, some c14, some c87, some c1046, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1229 : lratChecker f1229 p1229 = .success := by decide +kernel
theorem unsat1229 : Unsatisfiable (PosFin 31) f1229 := by
  apply lratCheckerSound f1229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1229
  · intro a ha; simp [p1229] at ha; subst a; trivial
  · exact checked1229
theorem derived1229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1229 := by
  apply localUnsat_implies_entails f1229 [c1227, c1221, c59, c750, c1200, c14, c87, c1046] c1229 unsat1229 (by rfl) a
  have h0 : Entails.eval a c1227 := derived1227 a h
  have h1 : Entails.eval a c1221 := derived1221 a h
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c750 := derived750 a h
  have h4 : Entails.eval a c1200 := derived1200 a h
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c1046 := derived1046 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1230 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1050, some c75, some c240, some c758, some c1037, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1230 : lratChecker f1230 p1230 = .success := by decide +kernel
theorem unsat1230 : Unsatisfiable (PosFin 31) f1230 := by
  apply lratCheckerSound f1230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1230
  · intro a ha; simp [p1230] at ha; subst a; trivial
  · exact checked1230
theorem derived1230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1230 := by
  apply localUnsat_implies_entails f1230 [c1184, c1050, c75, c240, c758, c1037] c1230 unsat1230 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1050 := derived1050 a h
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c758 := derived758 a h
  have h5 : Entails.eval a c1037 := derived1037 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1231 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1221, some c1227, some c1228, some c1230, some c18, some c1229, some c1200, some c1056, some c14, some c269, some c349, some c575, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1231 : lratChecker f1231 p1231 = .success := by decide +kernel
theorem unsat1231 : Unsatisfiable (PosFin 31) f1231 := by
  apply lratCheckerSound f1231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1231
  · intro a ha; simp [p1231] at ha; subst a; trivial
  · exact checked1231
theorem derived1231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1231 := by
  apply localUnsat_implies_entails f1231 [c1184, c1216, c1221, c1227, c1228, c1230, c18, c1229, c1200, c1056, c14, c269, c349, c575] c1231 unsat1231 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1221 := derived1221 a h
  have h3 : Entails.eval a c1227 := derived1227 a h
  have h4 : Entails.eval a c1228 := derived1228 a h
  have h5 : Entails.eval a c1230 := derived1230 a h
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c1229 := derived1229 a h
  have h8 : Entails.eval a c1200 := derived1200 a h
  have h9 : Entails.eval a c1056 := derived1056 a h
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c269 := h 268 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c575 := h 574 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1232 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1216, some c67, some c1056, some c269, some c35, some c1200, some c134, some c633, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1232 : lratChecker f1232 p1232 = .success := by decide +kernel
theorem unsat1232 : Unsatisfiable (PosFin 31) f1232 := by
  apply lratCheckerSound f1232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1232
  · intro a ha; simp [p1232] at ha; subst a; trivial
  · exact checked1232
theorem derived1232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1232 := by
  apply localUnsat_implies_entails f1232 [c1216, c67, c1056, c269, c35, c1200, c134, c633] c1232 unsat1232 (by rfl) a
  have h0 : Entails.eval a c1216 := derived1216 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c1056 := derived1056 a h
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c1200 := derived1200 a h
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c633 := h 632 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1233 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1231, some c1216, some c67, some c1056, some c1222, some c269, some c1232, some c82, some c13, some c572, some c1119, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1233 : lratChecker f1233 p1233 = .success := by decide +kernel
theorem unsat1233 : Unsatisfiable (PosFin 31) f1233 := by
  apply lratCheckerSound f1233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1233
  · intro a ha; simp [p1233] at ha; subst a; trivial
  · exact checked1233
theorem derived1233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1233 := by
  apply localUnsat_implies_entails f1233 [c1184, c1231, c1216, c67, c1056, c1222, c269, c1232, c82, c13, c572, c1119] c1233 unsat1233 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1231 := derived1231 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c1056 := derived1056 a h
  have h5 : Entails.eval a c1222 := derived1222 a h
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c1232 := derived1232 a h
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c572 := h 571 (by decide)
  have h11 : Entails.eval a c1119 := derived1119 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1234 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1233, some c1231, some c82, some c1047, some c18, some c1075, some c1084, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1234 : lratChecker f1234 p1234 = .success := by decide +kernel
theorem unsat1234 : Unsatisfiable (PosFin 31) f1234 := by
  apply lratCheckerSound f1234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1234
  · intro a ha; simp [p1234] at ha; subst a; trivial
  · exact checked1234
theorem derived1234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1234 := by
  apply localUnsat_implies_entails f1234 [c1184, c1233, c1231, c82, c1047, c18, c1075, c1084] c1234 unsat1234 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1233 := derived1233 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c1047 := derived1047 a h
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c1075 := derived1075 a h
  have h7 : Entails.eval a c1084 := derived1084 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1235 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1049, some c138, some c1035, some c160, some c1113, some c463, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1235 : lratChecker f1235 p1235 = .success := by decide +kernel
theorem unsat1235 : Unsatisfiable (PosFin 31) f1235 := by
  apply lratCheckerSound f1235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1235
  · intro a ha; simp [p1235] at ha; subst a; trivial
  · exact checked1235
theorem derived1235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1235 := by
  apply localUnsat_implies_entails f1235 [c1049, c138, c1035, c160, c1113, c463] c1235 unsat1235 (by rfl) a
  have h0 : Entails.eval a c1049 := derived1049 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c1035 := derived1035 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c1113 := derived1113 a h
  have h5 : Entails.eval a c463 := h 462 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1236 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1233, some c1231, some c1216, some c1234, some c1200, some c1235, some c78, some c226, some c134, some c1037, some c35, some c34, some c205, some c241, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1236 : lratChecker f1236 p1236 = .success := by decide +kernel
theorem unsat1236 : Unsatisfiable (PosFin 31) f1236 := by
  apply lratCheckerSound f1236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1236
  · intro a ha; simp [p1236] at ha; subst a; trivial
  · exact checked1236
theorem derived1236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1236 := by
  apply localUnsat_implies_entails f1236 [c1184, c1233, c1231, c1216, c1234, c1200, c1235, c78, c226, c134, c1037, c35, c34, c205, c241] c1236 unsat1236 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1233 := derived1233 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1216 := derived1216 a h
  have h4 : Entails.eval a c1234 := derived1234 a h
  have h5 : Entails.eval a c1200 := derived1200 a h
  have h6 : Entails.eval a c1235 := derived1235 a h
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c226 := h 225 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c1037 := derived1037 a h
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1237 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1236, some c1216, some c78, some c226, some c221, some c1066, some c220, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1237 : lratChecker f1237 p1237 = .success := by decide +kernel
theorem unsat1237 : Unsatisfiable (PosFin 31) f1237 := by
  apply lratCheckerSound f1237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1237
  · intro a ha; simp [p1237] at ha; subst a; trivial
  · exact checked1237
theorem derived1237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1237 := by
  apply localUnsat_implies_entails f1237 [c1184, c1236, c1216, c78, c226, c221, c1066, c220] c1237 unsat1237 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1236 := derived1236 a h
  have h2 : Entails.eval a c1216 := derived1216 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c226 := h 225 (by decide)
  have h5 : Entails.eval a c221 := h 220 (by decide)
  have h6 : Entails.eval a c1066 := derived1066 a h
  have h7 : Entails.eval a c220 := h 219 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1238 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1049, some c138, some c1235, some c236, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1238 : lratChecker f1238 p1238 = .success := by decide +kernel
theorem unsat1238 : Unsatisfiable (PosFin 31) f1238 := by
  apply lratCheckerSound f1238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1238
  · intro a ha; simp [p1238] at ha; subst a; trivial
  · exact checked1238
theorem derived1238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1238 := by
  apply localUnsat_implies_entails f1238 [c1049, c138, c1235, c236] c1238 unsat1238 (by rfl) a
  have h0 : Entails.eval a c1049 := derived1049 a h
  have h1 : Entails.eval a c138 := h 137 (by decide)
  have h2 : Entails.eval a c1235 := derived1235 a h
  have h3 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1239 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1231, some c1216, some c1233, some c1236, some c1237, some c1049, some c1059, some c1225, some c470, some c1125, some c1238, some c188, some c101, some c1051, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1239 : lratChecker f1239 p1239 = .success := by decide +kernel
theorem unsat1239 : Unsatisfiable (PosFin 31) f1239 := by
  apply lratCheckerSound f1239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1239
  · intro a ha; simp [p1239] at ha; subst a; trivial
  · exact checked1239
theorem derived1239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1239 := by
  apply localUnsat_implies_entails f1239 [c1231, c1216, c1233, c1236, c1237, c1049, c1059, c1225, c470, c1125, c1238, c188, c101, c1051] c1239 unsat1239 (by rfl) a
  have h0 : Entails.eval a c1231 := derived1231 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1233 := derived1233 a h
  have h3 : Entails.eval a c1236 := derived1236 a h
  have h4 : Entails.eval a c1237 := derived1237 a h
  have h5 : Entails.eval a c1049 := derived1049 a h
  have h6 : Entails.eval a c1059 := derived1059 a h
  have h7 : Entails.eval a c1225 := derived1225 a h
  have h8 : Entails.eval a c470 := h 469 (by decide)
  have h9 : Entails.eval a c1125 := derived1125 a h
  have h10 : Entails.eval a c1238 := derived1238 a h
  have h11 : Entails.eval a c188 := h 187 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c1051 := derived1051 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1240 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨26, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1239, some c1068, some c1231, some c1060, some c1045, some c1049, some c1058, some c1125, some c76, some c1035, some c698, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1240 : lratChecker f1240 p1240 = .success := by decide +kernel
theorem unsat1240 : Unsatisfiable (PosFin 31) f1240 := by
  apply lratCheckerSound f1240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1240
  · intro a ha; simp [p1240] at ha; subst a; trivial
  · exact checked1240
theorem derived1240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1240 := by
  apply localUnsat_implies_entails f1240 [c1184, c1216, c1239, c1068, c1231, c1060, c1045, c1049, c1058, c1125, c76, c1035, c698] c1240 unsat1240 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1239 := derived1239 a h
  have h3 : Entails.eval a c1068 := derived1068 a h
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c1060 := derived1060 a h
  have h6 : Entails.eval a c1045 := derived1045 a h
  have h7 : Entails.eval a c1049 := derived1049 a h
  have h8 : Entails.eval a c1058 := derived1058 a h
  have h9 : Entails.eval a c1125 := derived1125 a h
  have h10 : Entails.eval a c76 := h 75 (by decide)
  have h11 : Entails.eval a c1035 := derived1035 a h
  have h12 : Entails.eval a c698 := h 697 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1241 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1239, some c1068, some c1240, some c67, some c1056, some c228, some c269, some c62, some c1038, some c1082, some c342, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1241 : lratChecker f1241 p1241 = .success := by decide +kernel
theorem unsat1241 : Unsatisfiable (PosFin 31) f1241 := by
  apply lratCheckerSound f1241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1241
  · intro a ha; simp [p1241] at ha; subst a; trivial
  · exact checked1241
theorem derived1241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1241 := by
  apply localUnsat_implies_entails f1241 [c1184, c1216, c1239, c1068, c1240, c67, c1056, c228, c269, c62, c1038, c1082, c342] c1241 unsat1241 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1239 := derived1239 a h
  have h3 : Entails.eval a c1068 := derived1068 a h
  have h4 : Entails.eval a c1240 := derived1240 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c1056 := derived1056 a h
  have h7 : Entails.eval a c228 := h 227 (by decide)
  have h8 : Entails.eval a c269 := h 268 (by decide)
  have h9 : Entails.eval a c62 := h 61 (by decide)
  have h10 : Entails.eval a c1038 := derived1038 a h
  have h11 : Entails.eval a c1082 := derived1082 a h
  have h12 : Entails.eval a c342 := h 341 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1242 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨26, by decide⟩, false), (⟨14, by decide⟩, true), (⟨5, by decide⟩, true), (⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c67, some c1056, some c269, some c1082, some c352, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p1242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1242 : lratChecker f1242 p1242 = .success := by decide +kernel
theorem unsat1242 : Unsatisfiable (PosFin 31) f1242 := by
  apply lratCheckerSound f1242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1242
  · intro a ha; simp [p1242] at ha; subst a; trivial
  · exact checked1242
theorem derived1242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1242 := by
  apply localUnsat_implies_entails f1242 [c1184, c67, c1056, c269, c1082, c352] c1242 unsat1242 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c1056 := derived1056 a h
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c1082 := derived1082 a h
  have h5 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1243 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1216, some c1231, some c1239, some c1068, some c1241, some c1242, some c1060, some c1045, some c1094, some c34, some c270, some c1082, some c546, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p1243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1243 : lratChecker f1243 p1243 = .success := by decide +kernel
theorem unsat1243 : Unsatisfiable (PosFin 31) f1243 := by
  apply lratCheckerSound f1243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1243
  · intro a ha; simp [p1243] at ha; subst a; trivial
  · exact checked1243
theorem derived1243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1243 := by
  apply localUnsat_implies_entails f1243 [c1184, c1216, c1231, c1239, c1068, c1241, c1242, c1060, c1045, c1094, c34, c270, c1082, c546] c1243 unsat1243 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1216 := derived1216 a h
  have h2 : Entails.eval a c1231 := derived1231 a h
  have h3 : Entails.eval a c1239 := derived1239 a h
  have h4 : Entails.eval a c1068 := derived1068 a h
  have h5 : Entails.eval a c1241 := derived1241 a h
  have h6 : Entails.eval a c1242 := derived1242 a h
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c1045 := derived1045 a h
  have h9 : Entails.eval a c1094 := derived1094 a h
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c1082 := derived1082 a h
  have h13 : Entails.eval a c546 := h 545 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1244 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨26, by decide⟩, false), (⟨27, by decide⟩, true), (⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1184, some c1060, some c28, some c1037, some c1036, some c230, some c180, some c231, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p1244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1244 : lratChecker f1244 p1244 = .success := by decide +kernel
theorem unsat1244 : Unsatisfiable (PosFin 31) f1244 := by
  apply lratCheckerSound f1244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1244
  · intro a ha; simp [p1244] at ha; subst a; trivial
  · exact checked1244
theorem derived1244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1244 := by
  apply localUnsat_implies_entails f1244 [c1184, c1060, c28, c1037, c1036, c230, c180, c231] c1244 unsat1244 (by rfl) a
  have h0 : Entails.eval a c1184 := derived1184 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1036 := derived1036 a h
  have h5 : Entails.eval a c230 := h 229 (by decide)
  have h6 : Entails.eval a c180 := h 179 (by decide)
  have h7 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1244

end CochromaticTwenty.Certificates.Z12Direct_5_8_7
