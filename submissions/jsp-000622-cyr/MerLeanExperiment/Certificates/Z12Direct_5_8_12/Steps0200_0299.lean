import MerLeanExperiment.Certificates.Z12Direct_5_8_12.Steps0100_0199

/-! Generated from the actual pinned z12direct_5_8_12-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_12
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1117 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1100, some c1082, some c1105, some c1112, some c78, some c1116, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1117 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 31) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c1100, c1082, c1105, c1112, c78, c1116] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c1100 := derived1100 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c1105 := derived1105 a h
  have h3 : Entails.eval a c1112 := derived1112 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c1116 := derived1116 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨12, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c158, some c207, some c493, some c257, some c26, some c853, some c91, some c502, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1118 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 31) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c1082, c158, c207, c493, c257, c26, c853, c91, c502] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c493 := h 492 (by decide)
  have h4 : Entails.eval a c257 := h 256 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c853 := h 852 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c502 := h 501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c50, some c1117, some c1100, some c158, some c1118, some c905, some c654, some c750, some c194, some c120, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1119 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 31) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c1082, c50, c1117, c1100, c158, c1118, c905, c654, c750, c194, c120] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c1118 := derived1118 a h
  have h6 : Entails.eval a c905 := h 904 (by decide)
  have h7 : Entails.eval a c654 := h 653 (by decide)
  have h8 : Entails.eval a c750 := h 749 (by decide)
  have h9 : Entails.eval a c194 := h 193 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨17, by decide⟩, false), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c194, some c120, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1120 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 31) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c194, c120] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1121 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c50, some c1100, some c654, some c750, some c1120, some c905, some c833, some c252, some c267, some c260, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1121 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 31) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c1082, c50, c1100, c654, c750, c1120, c905, c833, c252, c267, c260] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c654 := h 653 (by decide)
  have h4 : Entails.eval a c750 := h 749 (by decide)
  have h5 : Entails.eval a c1120 := derived1120 a h
  have h6 : Entails.eval a c905 := h 904 (by decide)
  have h7 : Entails.eval a c833 := h 832 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c267 := h 266 (by decide)
  have h10 : Entails.eval a c260 := h 259 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c50, some c1117, some c1100, some c63, some c1119, some c1121, some c207, some c303, some c772, some c26, some c83, some c327, some c493, some c307, some c853, some c178, some c248, some c810, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1122 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 31) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c1082, c50, c1117, c1100, c63, c1119, c1121, c207, c303, c772, c26, c83, c327, c493, c307, c853, c178, c248, c810] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c1119 := derived1119 a h
  have h6 : Entails.eval a c1121 := derived1121 a h
  have h7 : Entails.eval a c207 := h 206 (by decide)
  have h8 : Entails.eval a c303 := h 302 (by decide)
  have h9 : Entails.eval a c772 := h 771 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c327 := h 326 (by decide)
  have h13 : Entails.eval a c493 := h 492 (by decide)
  have h14 : Entails.eval a c307 := h 306 (by decide)
  have h15 : Entails.eval a c853 := h 852 (by decide)
  have h16 : Entails.eval a c178 := h 177 (by decide)
  have h17 : Entails.eval a c248 := h 247 (by decide)
  have h18 : Entails.eval a c810 := h 809 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨20, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c50, some c207, some c303, some c772, some c26, some c525, some c493, some c307, some c284, some c343, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1123 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 31) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c1082, c50, c207, c303, c772, c26, c525, c493, c307, c284, c343] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c207 := h 206 (by decide)
  have h3 : Entails.eval a c303 := h 302 (by decide)
  have h4 : Entails.eval a c772 := h 771 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c525 := h 524 (by decide)
  have h7 : Entails.eval a c493 := h 492 (by decide)
  have h8 : Entails.eval a c307 := h 306 (by decide)
  have h9 : Entails.eval a c284 := h 283 (by decide)
  have h10 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1117, some c1100, some c1082, some c50, some c1122, some c1123, some c22, some c21, some c654, some c1121, some c608, some c750, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1124 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 31) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c1117, c1100, c1082, c50, c1122, c1123, c22, c21, c654, c1121, c608, c750] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c1117 := derived1117 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c1122 := derived1122 a h
  have h5 : Entails.eval a c1123 := derived1123 a h
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c654 := h 653 (by decide)
  have h9 : Entails.eval a c1121 := derived1121 a h
  have h10 : Entails.eval a c608 := h 607 (by decide)
  have h11 : Entails.eval a c750 := h 749 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨7, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c152, some c259, some c314, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1125 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 31) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c152, c259, c314] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c259 := h 258 (by decide)
  have h2 : Entails.eval a c314 := h 313 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1100, some c1082, some c1117, some c1125, some c1124, some c78, some c67, some c133, some c80, some c187, some c103, some c22, some c21, some c751, some c589, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1126 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 31) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c1100, c1082, c1117, c1125, c1124, c78, c67, c133, c80, c187, c103, c22, c21, c751, c589] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c1100 := derived1100 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c1125 := derived1125 a h
  have h4 : Entails.eval a c1124 := derived1124 a h
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c80 := h 79 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c751 := h 750 (by decide)
  have h14 : Entails.eval a c589 := h 588 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1126, some c78, some c46, some c1100, some c22, some c21, some c252, some c363, some c307, some c72, some c115, some c366, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1127 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 31) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c1082, c1126, c78, c46, c1100, c22, c21, c252, c363, c307, c72, c115, c366] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1126 := derived1126 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c1100 := derived1100 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c252 := h 251 (by decide)
  have h8 : Entails.eval a c363 := h 362 (by decide)
  have h9 : Entails.eval a c307 := h 306 (by decide)
  have h10 : Entails.eval a c72 := h 71 (by decide)
  have h11 : Entails.eval a c115 := h 114 (by decide)
  have h12 : Entails.eval a c366 := h 365 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨7, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c91, some c366, some c550, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1128 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 31) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c1082, c91, c366, c550] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  have h2 : Entails.eval a c366 := h 365 (by decide)
  have h3 : Entails.eval a c550 := h 549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c743, some c550, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1129 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 31) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c743, c550] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c743 := h 742 (by decide)
  have h1 : Entails.eval a c550 := h 549 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1130 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1127, some c187, some c80, some c1082, some c1126, some c78, some c46, some c1100, some c1128, some c1129, some c363, some c307, some c686, some c115, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1130 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 31) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c1127, c187, c80, c1082, c1126, c78, c46, c1100, c1128, c1129, c363, c307, c686, c115] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c1127 := derived1127 a h
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c1126 := derived1126 a h
  have h5 : Entails.eval a c78 := h 77 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c1100 := derived1100 a h
  have h8 : Entails.eval a c1128 := derived1128 a h
  have h9 : Entails.eval a c1129 := derived1129 a h
  have h10 : Entails.eval a c363 := h 362 (by decide)
  have h11 : Entails.eval a c307 := h 306 (by decide)
  have h12 : Entails.eval a c686 := h 685 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1126, some c1100, some c1082, some c78, some c46, some c1127, some c187, some c80, some c1130, some c77, some c167, some c252, some c723, some c45, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1131 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 31) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c1126, c1100, c1082, c78, c46, c1127, c187, c80, c1130, c77, c167, c252, c723, c45] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c1126 := derived1126 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c1127 := derived1127 a h
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c1130 := derived1130 a h
  have h9 : Entails.eval a c77 := h 76 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c723 := h 722 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c532, some c352, some c845, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false))]
def p1132 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 31) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c532, c352, c845] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c532 := h 531 (by decide)
  have h1 : Entails.eval a c352 := h 351 (by decide)
  have h2 : Entails.eval a c845 := h 844 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨18, by decide⟩, true), (⟨13, by decide⟩, false), (⟨16, by decide⟩, true), (⟨5, by decide⟩, true), (⟨11, by decide⟩, false), (⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨2, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c227, some c201, some c321, some c355, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1133 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 31) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c26, c227, c201, c321, c355] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c227 := h 226 (by decide)
  have h2 : Entails.eval a c201 := h 200 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1131, some c1126, some c1100, some c1082, some c77, some c143, some c252, some c26, some c1033, some c1132, some c104, some c1133, some c28, some c241, some c22, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1134 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 31) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c1131, c1126, c1100, c1082, c77, c143, c252, c26, c1033, c1132, c104, c1133, c28, c241, c22] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c1131 := derived1131 a h
  have h1 : Entails.eval a c1126 := derived1126 a h
  have h2 : Entails.eval a c1100 := derived1100 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c143 := h 142 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c1033 := derived1033 a h
  have h9 : Entails.eval a c1132 := derived1132 a h
  have h10 : Entails.eval a c104 := h 103 (by decide)
  have h11 : Entails.eval a c1133 := derived1133 a h
  have h12 : Entails.eval a c28 := h 27 (by decide)
  have h13 : Entails.eval a c241 := h 240 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨13, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c28, some c241, some c22, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1135 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 31) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c28, c241, c22] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c86, some c99, some c83, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1136 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 31) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c86, c99, c83] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1134, some c1131, some c1126, some c1100, some c1082, some c26, some c1129, some c1135, some c227, some c846, some c63, some c1136, some c58, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1137 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 31) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c1134, c1131, c1126, c1100, c1082, c26, c1129, c1135, c227, c846, c63, c1136, c58] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c1134 := derived1134 a h
  have h1 : Entails.eval a c1131 := derived1131 a h
  have h2 : Entails.eval a c1126 := derived1126 a h
  have h3 : Entails.eval a c1100 := derived1100 a h
  have h4 : Entails.eval a c1082 := derived1082 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c1129 := derived1129 a h
  have h7 : Entails.eval a c1135 := derived1135 a h
  have h8 : Entails.eval a c227 := h 226 (by decide)
  have h9 : Entails.eval a c846 := h 845 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c1136 := derived1136 a h
  have h12 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1137, some c1134, some c1131, some c1126, some c1082, some c227, some c846, some c484, some c136, some c504, some c278, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1138 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 31) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c1137, c1134, c1131, c1126, c1082, c227, c846, c484, c136, c504, c278] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c1137 := derived1137 a h
  have h1 : Entails.eval a c1134 := derived1134 a h
  have h2 : Entails.eval a c1131 := derived1131 a h
  have h3 : Entails.eval a c1126 := derived1126 a h
  have h4 : Entails.eval a c1082 := derived1082 a h
  have h5 : Entails.eval a c227 := h 226 (by decide)
  have h6 : Entails.eval a c846 := h 845 (by decide)
  have h7 : Entails.eval a c484 := h 483 (by decide)
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c504 := h 503 (by decide)
  have h10 : Entails.eval a c278 := h 277 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1138, some c1134, some c1131, some c1126, some c1100, some c1082, some c63, some c241, some c1136, some c58, some c147, some c900, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1139 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 31) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c1138, c1134, c1131, c1126, c1100, c1082, c63, c241, c1136, c58, c147, c900] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c1138 := derived1138 a h
  have h1 : Entails.eval a c1134 := derived1134 a h
  have h2 : Entails.eval a c1131 := derived1131 a h
  have h3 : Entails.eval a c1126 := derived1126 a h
  have h4 : Entails.eval a c1100 := derived1100 a h
  have h5 : Entails.eval a c1082 := derived1082 a h
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c241 := h 240 (by decide)
  have h8 : Entails.eval a c1136 := derived1136 a h
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c900 := h 899 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c256, some c311, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1140 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 31) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c256, c311] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c256 := h 255 (by decide)
  have h1 : Entails.eval a c311 := h 310 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1141 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨20, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c307, some c1140, some c45, some c343, some c589, some c805, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true))]
def p1141 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 31) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c307, c1140, c45, c343, c589, c805] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c1140 := derived1140 a h
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c343 := h 342 (by decide)
  have h4 : Entails.eval a c589 := h 588 (by decide)
  have h5 : Entails.eval a c805 := h 804 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨12, by decide⟩, true), (⟨25, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c147, some c171, some c139, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1142 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 31) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c147, c171, c139] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c147 := h 146 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1137, some c1134, some c1131, some c1126, some c1100, some c1082, some c1138, some c1139, some c46, some c1141, some c368, some c1142, some c256, some c284, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1143 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 31) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c1137, c1134, c1131, c1126, c1100, c1082, c1138, c1139, c46, c1141, c368, c1142, c256, c284] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c1137 := derived1137 a h
  have h1 : Entails.eval a c1134 := derived1134 a h
  have h2 : Entails.eval a c1131 := derived1131 a h
  have h3 : Entails.eval a c1126 := derived1126 a h
  have h4 : Entails.eval a c1100 := derived1100 a h
  have h5 : Entails.eval a c1082 := derived1082 a h
  have h6 : Entails.eval a c1138 := derived1138 a h
  have h7 : Entails.eval a c1139 := derived1139 a h
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c1141 := derived1141 a h
  have h10 : Entails.eval a c368 := h 367 (by decide)
  have h11 : Entails.eval a c1142 := derived1142 a h
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c284 := h 283 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 31 := directClause [(⟨2, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1100, some c1126, some c1131, some c1134, some c1137, some c1143, some c524, some c284, some c343, some c147, some c232, some c285, some c889, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1144 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 31) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c1082, c1100, c1126, c1131, c1134, c1137, c1143, c524, c284, c343, c147, c232, c285, c889] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1100 := derived1100 a h
  have h2 : Entails.eval a c1126 := derived1126 a h
  have h3 : Entails.eval a c1131 := derived1131 a h
  have h4 : Entails.eval a c1134 := derived1134 a h
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1143 := derived1143 a h
  have h7 : Entails.eval a c524 := h 523 (by decide)
  have h8 : Entails.eval a c284 := h 283 (by decide)
  have h9 : Entails.eval a c343 := h 342 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c232 := h 231 (by decide)
  have h12 : Entails.eval a c285 := h 284 (by decide)
  have h13 : Entails.eval a c889 := h 888 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c1082, some c147, some c524, some c841, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1145 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 31) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c1144, c1082, c147, c524, c841] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c524 := h 523 (by decide)
  have h4 : Entails.eval a c841 := h 840 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 31 := directClause [(⟨13, by decide⟩, true), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c30, some c1145, some c78, some c80, some c864, some c785, some c76, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1146 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 31) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1144, c30, c1145, c78, c80, c864, c785, c76] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c1145 := derived1145 a h
  have h3 : Entails.eval a c78 := h 77 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c864 := h 863 (by decide)
  have h6 : Entails.eval a c785 := h 784 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c1082, some c78, some c187, some c46, some c22, some c363, some c224, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1147 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 31) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c1144, c1082, c78, c187, c46, c22, c363, c224] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c187 := h 186 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c363 := h 362 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c1082, some c1146, some c1147, some c147, some c99, some c1136, some c139, some c764, some c746, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1148 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 31) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c1144, c1082, c1146, c1147, c147, c99, c1136, c139, c764, c746] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c1146 := derived1146 a h
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c1136 := derived1136 a h
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c764 := h 763 (by decide)
  have h9 : Entails.eval a c746 := h 745 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1147, some c1148, some c1144, some c1082, some c46, some c256, some c53, some c5, some c1140, some c217, some c844, some c414, some c479, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1149 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 31) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c1147, c1148, c1144, c1082, c46, c256, c53, c5, c1140, c217, c844, c414, c479] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c53 := h 52 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c1140 := derived1140 a h
  have h9 : Entails.eval a c217 := h 216 (by decide)
  have h10 : Entails.eval a c844 := h 843 (by decide)
  have h11 : Entails.eval a c414 := h 413 (by decide)
  have h12 : Entails.eval a c479 := h 478 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1150 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1148, some c1144, some c1149, some c1136, some c775, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1150 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 31) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1148, c1144, c1149, c1136, c775] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1148 := derived1148 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1149 := derived1149 a h
  have h3 : Entails.eval a c1136 := derived1136 a h
  have h4 : Entails.eval a c775 := h 774 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1150, some c1148, some c1144, some c1082, some c78, some c774, some c524, some c304, some c1140, some c331, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1151 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 31) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1150, c1148, c1144, c1082, c78, c774, c524, c304, c1140, c331] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1150 := derived1150 a h
  have h1 : Entails.eval a c1148 := derived1148 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c774 := h 773 (by decide)
  have h6 : Entails.eval a c524 := h 523 (by decide)
  have h7 : Entails.eval a c304 := h 303 (by decide)
  have h8 : Entails.eval a c1140 := derived1140 a h
  have h9 : Entails.eval a c331 := h 330 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c1082, some c1148, some c1151, some c46, some c5, some c1140, some c910, some c572, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1152 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 31) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c1144, c1082, c1148, c1151, c46, c5, c1140, c910, c572] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c1148 := derived1148 a h
  have h3 : Entails.eval a c1151 := derived1151 a h
  have h4 : Entails.eval a c46 := h 45 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c1140 := derived1140 a h
  have h7 : Entails.eval a c910 := h 909 (by decide)
  have h8 : Entails.eval a c572 := h 571 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1152, some c1144, some c1082, some c422, some c493, some c22, some c888, some c5, some c50, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1153 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 31) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1152, c1144, c1082, c422, c493, c22, c888, c5, c50] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c422 := h 421 (by decide)
  have h4 : Entails.eval a c493 := h 492 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c888 := h 887 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1152, some c1144, some c1082, some c1153, some c304, some c1140, some c331, some c380, some c50, some c152, some c165, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1154 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 31) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c1152, c1144, c1082, c1153, c304, c1140, c331, c380, c50, c152, c165] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c1153 := derived1153 a h
  have h4 : Entails.eval a c304 := h 303 (by decide)
  have h5 : Entails.eval a c1140 := derived1140 a h
  have h6 : Entails.eval a c331 := h 330 (by decide)
  have h7 : Entails.eval a c380 := h 379 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1152, some c1144, some c1082, some c1154, some c78, some c774, some c304, some c1140, some c331, some c50, some c152, some c4, some c1125, some c409, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1155 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 31) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1152, c1144, c1082, c1154, c78, c774, c304, c1140, c331, c50, c152, c4, c1125, c409] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c1154 := derived1154 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c774 := h 773 (by decide)
  have h6 : Entails.eval a c304 := h 303 (by decide)
  have h7 : Entails.eval a c1140 := derived1140 a h
  have h8 : Entails.eval a c331 := h 330 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c4 := h 3 (by decide)
  have h12 : Entails.eval a c1125 := derived1125 a h
  have h13 : Entails.eval a c409 := h 408 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨25, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1152, some c1144, some c1082, some c152, some c52, some c1125, some c136, some c274, some c398, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1156 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 31) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c1152, c1144, c1082, c152, c52, c1125, c136, c274, c398] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c1152 := derived1152 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c152 := h 151 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c1125 := derived1125 a h
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c398 := h 397 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨15, by decide⟩, false), (⟨25, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c78, some c1156, some c50, some c1155, some c1144, some c435, some c94, some c804, some c471, some c761, some c373, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1157 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 31) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c1082, c78, c1156, c50, c1155, c1144, c435, c94, c804, c471, c761, c373] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c1156 := derived1156 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c1155 := derived1155 a h
  have h5 : Entails.eval a c1144 := derived1144 a h
  have h6 : Entails.eval a c435 := h 434 (by decide)
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c804 := h 803 (by decide)
  have h9 : Entails.eval a c471 := h 470 (by decide)
  have h10 : Entails.eval a c761 := h 760 (by decide)
  have h11 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨25, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1156, some c78, some c1155, some c1144, some c1082, some c1157, some c1136, some c71, some c908, some c765, some c804, some c197, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1158 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 31) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c1156, c78, c1155, c1144, c1082, c1157, c1136, c71, c908, c765, c804, c197] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c1155 := derived1155 a h
  have h3 : Entails.eval a c1144 := derived1144 a h
  have h4 : Entails.eval a c1082 := derived1082 a h
  have h5 : Entails.eval a c1157 := derived1157 a h
  have h6 : Entails.eval a c1136 := derived1136 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c908 := h 907 (by decide)
  have h9 : Entails.eval a c765 := h 764 (by decide)
  have h10 : Entails.eval a c804 := h 803 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1155, some c1152, some c1144, some c1082, some c78, some c1156, some c50, some c1158, some c493, some c565, some c29, some c335, some c804, some c310, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1159 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 31) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c1155, c1152, c1144, c1082, c78, c1156, c50, c1158, c493, c565, c29, c335, c804, c310] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c1155 := derived1155 a h
  have h1 : Entails.eval a c1152 := derived1152 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c1156 := derived1156 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c1158 := derived1158 a h
  have h8 : Entails.eval a c493 := h 492 (by decide)
  have h9 : Entails.eval a c565 := h 564 (by decide)
  have h10 : Entails.eval a c29 := h 28 (by decide)
  have h11 : Entails.eval a c335 := h 334 (by decide)
  have h12 : Entails.eval a c804 := h 803 (by decide)
  have h13 : Entails.eval a c310 := h 309 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c50, some c1159, some c1155, some c1152, some c1144, some c493, some c22, some c814, some c29, some c335, some c337, some c368, some c275, some c310, some c336, some c489, some c122, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1160 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 31) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c1082, c50, c1159, c1155, c1152, c1144, c493, c22, c814, c29, c335, c337, c368, c275, c310, c336, c489, c122] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c1159 := derived1159 a h
  have h3 : Entails.eval a c1155 := derived1155 a h
  have h4 : Entails.eval a c1152 := derived1152 a h
  have h5 : Entails.eval a c1144 := derived1144 a h
  have h6 : Entails.eval a c493 := h 492 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c814 := h 813 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c335 := h 334 (by decide)
  have h11 : Entails.eval a c337 := h 336 (by decide)
  have h12 : Entails.eval a c368 := h 367 (by decide)
  have h13 : Entails.eval a c275 := h 274 (by decide)
  have h14 : Entails.eval a c310 := h 309 (by decide)
  have h15 : Entails.eval a c336 := h 335 (by decide)
  have h16 : Entails.eval a c489 := h 488 (by decide)
  have h17 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨16, by decide⟩, false), (⟨3, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c880, some c452, some c68, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p1161 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 31) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c880, c452, c68] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c880 := h 879 (by decide)
  have h1 : Entails.eval a c452 := h 451 (by decide)
  have h2 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c307, some c197, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1162 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 31) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c307, c197] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c307 := h 306 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1163 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨14, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨21, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c525, some c1161, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1163 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 31) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c525, c1161] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c525 := h 524 (by decide)
  have h1 : Entails.eval a c1161 := derived1161 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1164 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨28, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1159, some c1144, some c1082, some c50, some c1160, some c1162, some c1163, some c29, some c272, some c726, some c534, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1164 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 31) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c1159, c1144, c1082, c50, c1160, c1162, c1163, c29, c272, c726, c534] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c1159 := derived1159 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c1160 := derived1160 a h
  have h5 : Entails.eval a c1162 := derived1162 a h
  have h6 : Entails.eval a c1163 := derived1163 a h
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c272 := h 271 (by decide)
  have h9 : Entails.eval a c726 := h 725 (by decide)
  have h10 : Entails.eval a c534 := h 533 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1155, some c1152, some c1144, some c1082, some c152, some c52, some c1125, some c274, some c32, some c58, some c197, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1165 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 31) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c1155, c1152, c1144, c1082, c152, c52, c1125, c274, c32, c58, c197] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c1155 := derived1155 a h
  have h1 : Entails.eval a c1152 := derived1152 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c1125 := derived1125 a h
  have h7 : Entails.eval a c274 := h 273 (by decide)
  have h8 : Entails.eval a c32 := h 31 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c1082, some c1152, some c1159, some c1165, some c1164, some c133, some c80, some c187, some c22, some c224, some c363, some c539, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1166 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 31) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c1144, c1082, c1152, c1159, c1165, c1164, c133, c80, c187, c22, c224, c363, c539] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c1152 := derived1152 a h
  have h3 : Entails.eval a c1159 := derived1159 a h
  have h4 : Entails.eval a c1165 := derived1165 a h
  have h5 : Entails.eval a c1164 := derived1164 a h
  have h6 : Entails.eval a c133 := h 132 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c363 := h 362 (by decide)
  have h12 : Entails.eval a c539 := h 538 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1144, some c335, some c273, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1167 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 31) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c1166, c1144, c335, c273] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c335 := h 334 (by decide)
  have h3 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c78, some c1166, some c1144, some c1082, some c22, some c187, some c80, some c133, some c551, some c857, some c727, some c146, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1168 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 31) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c78, c1166, c1144, c1082, c22, c187, c80, c133, c551, c857, c727, c146] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c1166 := derived1166 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c551 := h 550 (by decide)
  have h9 : Entails.eval a c857 := h 856 (by decide)
  have h10 : Entails.eval a c727 := h 726 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c78, some c1166, some c1144, some c1082, some c1168, some c29, some c273, some c1167, some c224, some c223, some c80, some c133, some c276, some c46, some c818, some c252, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1169 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 31) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c78, c1166, c1144, c1082, c1168, c29, c273, c1167, c224, c223, c80, c133, c276, c46, c818, c252] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c1166 := derived1166 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c1168 := derived1168 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c1167 := derived1167 a h
  have h8 : Entails.eval a c224 := h 223 (by decide)
  have h9 : Entails.eval a c223 := h 222 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c133 := h 132 (by decide)
  have h12 : Entails.eval a c276 := h 275 (by decide)
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c818 := h 817 (by decide)
  have h15 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨15, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c78, some c1166, some c1144, some c1082, some c29, some c224, some c223, some c80, some c133, some c46, some c660, some c252, some c818, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1170 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 31) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c78, c1166, c1144, c1082, c29, c224, c223, c80, c133, c46, c660, c252, c818] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c1166 := derived1166 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c224 := h 223 (by decide)
  have h6 : Entails.eval a c223 := h 222 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c660 := h 659 (by decide)
  have h11 : Entails.eval a c252 := h 251 (by decide)
  have h12 : Entails.eval a c818 := h 817 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1169, some c78, some c1166, some c1144, some c1082, some c1170, some c197, some c22, some c187, some c80, some c745, some c93, some c133, some c19, some c973, some c4, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1171 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 31) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c1169, c78, c1166, c1144, c1082, c1170, c197, c22, c187, c80, c745, c93, c133, c19, c973, c4] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c1169 := derived1169 a h
  have h1 : Entails.eval a c78 := h 77 (by decide)
  have h2 : Entails.eval a c1166 := derived1166 a h
  have h3 : Entails.eval a c1144 := derived1144 a h
  have h4 : Entails.eval a c1082 := derived1082 a h
  have h5 : Entails.eval a c1170 := derived1170 a h
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c187 := h 186 (by decide)
  have h9 : Entails.eval a c80 := h 79 (by decide)
  have h10 : Entails.eval a c745 := h 744 (by decide)
  have h11 : Entails.eval a c93 := h 92 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c19 := h 18 (by decide)
  have h14 : Entails.eval a c973 := derived973 a h
  have h15 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1166, some c1082, some c78, some c1171, some c1167, some c22, some c187, some c80, some c133, some c46, some c167, some c146, some c727, some c533, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1172 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 31) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c1166, c1082, c78, c1171, c1167, c22, c187, c80, c133, c46, c167, c146, c727, c533] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c1166 := derived1166 a h
  have h1 : Entails.eval a c1082 := derived1082 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c1171 := derived1171 a h
  have h4 : Entails.eval a c1167 := derived1167 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c187 := h 186 (by decide)
  have h7 : Entails.eval a c80 := h 79 (by decide)
  have h8 : Entails.eval a c133 := h 132 (by decide)
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c167 := h 166 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c727 := h 726 (by decide)
  have h13 : Entails.eval a c533 := h 532 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1172, some c1167, some c26, some c1144, some c22, some c222, some c207, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1173 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 31) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c1082, c1172, c1167, c26, c1144, c22, c222, c207] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c1167 := derived1167 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c1144 := derived1144 a h
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c222 := h 221 (by decide)
  have h7 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1172, some c1166, some c1082, some c1167, some c26, some c1173, some c190, some c83, some c136, some c50, some c551, some c33, some c744, some c178, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1174 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 31) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c1172, c1166, c1082, c1167, c26, c1173, c190, c83, c136, c50, c551, c33, c744, c178] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c1172 := derived1172 a h
  have h1 : Entails.eval a c1166 := derived1166 a h
  have h2 : Entails.eval a c1082 := derived1082 a h
  have h3 : Entails.eval a c1167 := derived1167 a h
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c1173 := derived1173 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c551 := h 550 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c744 := h 743 (by decide)
  have h13 : Entails.eval a c178 := h 177 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1082, some c1172, some c26, some c1174, some c1166, some c1144, some c190, some c221, some c83, some c126, some c136, some c744, some c551, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1175 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 31) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c1082, c1172, c26, c1174, c1166, c1144, c190, c221, c83, c126, c136, c744, c551] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c1082 := derived1082 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c1174 := derived1174 a h
  have h4 : Entails.eval a c1166 := derived1166 a h
  have h5 : Entails.eval a c1144 := derived1144 a h
  have h6 : Entails.eval a c190 := h 189 (by decide)
  have h7 : Entails.eval a c221 := h 220 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c744 := h 743 (by decide)
  have h12 : Entails.eval a c551 := h 550 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1174, some c1172, some c1144, some c1082, some c197, some c26, some c1175, some c22, some c28, some c1091, some c207, some c629, some c580, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1176 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 31) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c1174, c1172, c1144, c1082, c197, c26, c1175, c22, c28, c1091, c207, c629, c580] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c1174 := derived1174 a h
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c1144 := derived1144 a h
  have h3 : Entails.eval a c1082 := derived1082 a h
  have h4 : Entails.eval a c197 := h 196 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c1175 := derived1175 a h
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c1091 := derived1091 a h
  have h10 : Entails.eval a c207 := h 206 (by decide)
  have h11 : Entails.eval a c629 := h 628 (by decide)
  have h12 : Entails.eval a c580 := h 579 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1172, some c1144, some c1176, some c29, some c1174, some c223, some c24, some c1166, some c273, some c48, some c4, some c1082, some c277, some c170, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1177 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 31) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c1172, c1144, c1176, c29, c1174, c223, c24, c1166, c273, c48, c4, c1082, c277, c170] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c1172 := derived1172 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1176 := derived1176 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c1174 := derived1174 a h
  have h5 : Entails.eval a c223 := h 222 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c1166 := derived1166 a h
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c1082 := derived1082 a h
  have h12 : Entails.eval a c277 := h 276 (by decide)
  have h13 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1174, some c1144, some c1176, some c223, some c1172, some c29, some c24, some c1166, some c273, some c1177, some c911, some c48, some c4, some c1082, some c703, some c254, some c334, some c307, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1178 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 31) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c1174, c1144, c1176, c223, c1172, c29, c24, c1166, c273, c1177, c911, c48, c4, c1082, c703, c254, c334, c307] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c1174 := derived1174 a h
  have h1 : Entails.eval a c1144 := derived1144 a h
  have h2 : Entails.eval a c1176 := derived1176 a h
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c1172 := derived1172 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c1166 := derived1166 a h
  have h8 : Entails.eval a c273 := h 272 (by decide)
  have h9 : Entails.eval a c1177 := derived1177 a h
  have h10 : Entails.eval a c911 := h 910 (by decide)
  have h11 : Entails.eval a c48 := h 47 (by decide)
  have h12 : Entails.eval a c4 := h 3 (by decide)
  have h13 : Entails.eval a c1082 := derived1082 a h
  have h14 : Entails.eval a c703 := h 702 (by decide)
  have h15 : Entails.eval a c254 := h 253 (by decide)
  have h16 : Entails.eval a c334 := h 333 (by decide)
  have h17 : Entails.eval a c307 := h 306 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1144, some c1166, some c1172, some c1174, some c1176, some c29, some c273, some c223, some c24, some c48, some c1177, some c911, some c306, some c1178, some c339, some c319, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1179 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 31) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c1144, c1166, c1172, c1174, c1176, c29, c273, c223, c24, c48, c1177, c911, c306, c1178, c339, c319] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c1144 := derived1144 a h
  have h1 : Entails.eval a c1166 := derived1166 a h
  have h2 : Entails.eval a c1172 := derived1172 a h
  have h3 : Entails.eval a c1174 := derived1174 a h
  have h4 : Entails.eval a c1176 := derived1176 a h
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c273 := h 272 (by decide)
  have h7 : Entails.eval a c223 := h 222 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c1177 := derived1177 a h
  have h11 : Entails.eval a c911 := h 910 (by decide)
  have h12 : Entails.eval a c306 := h 305 (by decide)
  have h13 : Entails.eval a c1178 := derived1178 a h
  have h14 : Entails.eval a c339 := h 338 (by decide)
  have h15 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c602, some c662, some c47, some c51, some c508, some c137, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1180 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 31) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c1179, c602, c662, c47, c51, c508, c137] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c602 := h 601 (by decide)
  have h2 : Entails.eval a c662 := h 661 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c508 := h 507 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c12, some c29, some c1180, some c52, some c309, some c524, some c31, some c436, some c502, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1181 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 31) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c12, c29, c1180, c52, c309, c524, c31, c436, c502] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c12 := h 11 (by decide)
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c1180 := derived1180 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c524 := h 523 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c436 := h 435 (by decide)
  have h8 : Entails.eval a c502 := h 501 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, false), (⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c309, some c277, some c524, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1182 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 31) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c29, c309, c277, c524] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c309 := h 308 (by decide)
  have h2 : Entails.eval a c277 := h 276 (by decide)
  have h3 : Entails.eval a c524 := h 523 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨2, by decide⟩, false), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c1181, some c600, some c1182, some c786, some c144, some c145, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1183 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 31) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1179, c1181, c600, c1182, c786, c144, c145] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1181 := derived1181 a h
  have h2 : Entails.eval a c600 := h 599 (by decide)
  have h3 : Entails.eval a c1182 := derived1182 a h
  have h4 : Entails.eval a c786 := h 785 (by decide)
  have h5 : Entails.eval a c144 := h 143 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1184 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, false), (⟨2, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c600, some c786, some c144, some c145, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1184 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 31) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1179, c600, c786, c144, c145] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c600 := h 599 (by decide)
  have h2 : Entails.eval a c786 := h 785 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c600, some c1184, some c182, some c277, some c693, some c145, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1185 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 31) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c1179, c600, c1184, c182, c277, c693, c145] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c600 := h 599 (by decide)
  have h2 : Entails.eval a c1184 := derived1184 a h
  have h3 : Entails.eval a c182 := h 181 (by decide)
  have h4 : Entails.eval a c277 := h 276 (by decide)
  have h5 : Entails.eval a c693 := h 692 (by decide)
  have h6 : Entails.eval a c145 := h 144 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨19, by decide⟩, true), (⟨28, by decide⟩, false), (⟨17, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c52, some c309, some c31, some c585, some c682, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1186 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 31) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c1179, c52, c309, c31, c585, c682] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c309 := h 308 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c585 := h 584 (by decide)
  have h5 : Entails.eval a c682 := h 681 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c12, some c1183, some c1185, some c1186, some c602, some c662, some c47, some c51, some c689, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1187 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 31) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c1179, c12, c1183, c1185, c1186, c602, c662, c47, c51, c689] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c12 := h 11 (by decide)
  have h2 : Entails.eval a c1183 := derived1183 a h
  have h3 : Entails.eval a c1185 := derived1185 a h
  have h4 : Entails.eval a c1186 := derived1186 a h
  have h5 : Entails.eval a c602 := h 601 (by decide)
  have h6 : Entails.eval a c662 := h 661 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c689 := h 688 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c47, some c282, some c678, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1188 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 31) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c1179, c47, c282, c678] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c282 := h 281 (by decide)
  have h3 : Entails.eval a c678 := h 677 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c47, some c51, some c232, some c1188, some c658, some c137, some c25, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1189 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 31) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c1179, c47, c51, c232, c1188, c658, c137, c25] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c1188 := derived1188 a h
  have h5 : Entails.eval a c658 := h 657 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨20, by decide⟩, false), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c585, some c252, some c232, some c455, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1190 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 31) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c1179, c585, c252, c232, c455] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c585 := h 584 (by decide)
  have h2 : Entails.eval a c252 := h 251 (by decide)
  have h3 : Entails.eval a c232 := h 231 (by decide)
  have h4 : Entails.eval a c455 := h 454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c1187, some c1189, some c52, some c309, some c617, some c1190, some c143, some c665, some c145, some c268, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1191 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 31) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c1179, c1187, c1189, c52, c309, c617, c1190, c143, c665, c145, c268] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1187 := derived1187 a h
  have h2 : Entails.eval a c1189 := derived1189 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c309 := h 308 (by decide)
  have h5 : Entails.eval a c617 := h 616 (by decide)
  have h6 : Entails.eval a c1190 := derived1190 a h
  have h7 : Entails.eval a c143 := h 142 (by decide)
  have h8 : Entails.eval a c665 := h 664 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c1191, some c1187, some c52, some c182, some c309, some c46, some c45, some c617, some c252, some c232, some c455, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1192 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 31) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c1179, c1191, c1187, c52, c182, c309, c46, c45, c617, c252, c232, c455] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1191 := derived1191 a h
  have h2 : Entails.eval a c1187 := derived1187 a h
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c182 := h 181 (by decide)
  have h5 : Entails.eval a c309 := h 308 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c45 := h 44 (by decide)
  have h8 : Entails.eval a c617 := h 616 (by decide)
  have h9 : Entails.eval a c252 := h 251 (by decide)
  have h10 : Entails.eval a c232 := h 231 (by decide)
  have h11 : Entails.eval a c455 := h 454 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 31 := directClause [(⟨7, by decide⟩, true), (⟨13, by decide⟩, true), (⟨11, by decide⟩, false), (⟨22, by decide⟩, true), (⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c145, some c617, some c252, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1193 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 31) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c1179, c145, c617, c252] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c145 := h 144 (by decide)
  have h2 : Entails.eval a c617 := h 616 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1194 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨26, by decide⟩, false), (⟨19, by decide⟩, false), (⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c2, some c914, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1194 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 31) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c2, c914] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c2 := h 1 (by decide)
  have h1 : Entails.eval a c914 := h 913 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1195 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, true), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c1187, some c1191, some c1192, some c144, some c47, some c51, some c232, some c1194, some c145, some c1193, some c109, some c784, some c894, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p1195 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 31) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c1179, c1187, c1191, c1192, c144, c47, c51, c232, c1194, c145, c1193, c109, c784, c894] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1187 := derived1187 a h
  have h2 : Entails.eval a c1191 := derived1191 a h
  have h3 : Entails.eval a c1192 := derived1192 a h
  have h4 : Entails.eval a c144 := h 143 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c232 := h 231 (by decide)
  have h8 : Entails.eval a c1194 := derived1194 a h
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c1193 := derived1193 a h
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c784 := h 783 (by decide)
  have h13 : Entails.eval a c894 := h 893 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c1195, some c197, some c27, some c28, some c268, some c26, some c385, some c213, some c746, some c552, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1196 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 31) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c1179, c1195, c197, c27, c28, c268, c26, c385, c213, c746, c552] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c197 := h 196 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c268 := h 267 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c213 := h 212 (by decide)
  have h9 : Entails.eval a c746 := h 745 (by decide)
  have h10 : Entails.eval a c552 := h 551 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨10, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c27, some c327, some c28, some c213, some c26, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1197 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 31) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c1179, c27, c327, c28, c213, c26] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c327 := h 326 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c213 := h 212 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1198 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c493, some c855, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1198 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 31) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c493, c855] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c493 := h 492 (by decide)
  have h1 : Entails.eval a c855 := h 854 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1199 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨4, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c204, some c1196, some c213, some c50, some c24, some c214, some c330, some c329, some c1198, some c342, some c789, some c902, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1199 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 31) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c1179, c204, c1196, c213, c50, c24, c214, c330, c329, c1198, c342, c789, c902] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c1196 := derived1196 a h
  have h3 : Entails.eval a c213 := h 212 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c214 := h 213 (by decide)
  have h7 : Entails.eval a c330 := h 329 (by decide)
  have h8 : Entails.eval a c329 := h 328 (by decide)
  have h9 : Entails.eval a c1198 := derived1198 a h
  have h10 : Entails.eval a c342 := h 341 (by decide)
  have h11 : Entails.eval a c789 := h 788 (by decide)
  have h12 : Entails.eval a c902 := h 901 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨16, by decide⟩, false), (⟨5, by decide⟩, false), (⟨10, by decide⟩, true), (⟨14, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c198, some c50, some c688, some c585, some c765, some c549, some c279, some c137, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 31) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c1179, c198, c50, c688, c585, c765, c549, c279, c137] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c688 := h 687 (by decide)
  have h4 : Entails.eval a c585 := h 584 (by decide)
  have h5 : Entails.eval a c765 := h 764 (by decide)
  have h6 : Entails.eval a c549 := h 548 (by decide)
  have h7 : Entails.eval a c279 := h 278 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1201 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c204, some c1196, some c1197, some c1199, some c25, some c236, some c198, some c1200, some c64, some c237, some c230, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 31) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c1179, c204, c1196, c1197, c1199, c25, c236, c198, c1200, c64, c237, c230] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c204 := h 203 (by decide)
  have h2 : Entails.eval a c1196 := derived1196 a h
  have h3 : Entails.eval a c1197 := derived1197 a h
  have h4 : Entails.eval a c1199 := derived1199 a h
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c236 := h 235 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c1200 := derived1200 a h
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c237 := h 236 (by decide)
  have h11 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨14, by decide⟩, false), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c1196, some c1197, some c204, some c1201, some c28, some c11, some c25, some c23, some c64, some c191, some c84, some c50, some c753, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 31) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c1179, c1196, c1197, c204, c1201, c28, c11, c25, c23, c64, c191, c84, c50, c753] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c1196 := derived1196 a h
  have h2 : Entails.eval a c1197 := derived1197 a h
  have h3 : Entails.eval a c204 := h 203 (by decide)
  have h4 : Entails.eval a c1201 := derived1201 a h
  have h5 : Entails.eval a c28 := h 27 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c191 := h 190 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  have h13 : Entails.eval a c753 := h 752 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1203 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨2, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c23, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 31) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c1179, c23] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1204 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c25, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p1204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 31) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c1179, c25] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1205 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c27, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 31) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c1179, c27] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1206 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨26, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c47, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 31) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c1179, c47] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1207 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨27, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c49, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p1207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 31) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c1179, c49] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1208 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c51, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 31) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c1179, c51] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c51 := h 50 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1209 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨21, by decide⟩, true), (⟨22, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c92, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 31) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c1179, c92] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1210 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c95, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 31) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c1179, c95] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1211 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨22, by decide⟩, false), (⟨13, by decide⟩, false), (⟨20, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c97, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 31) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c1179, c97] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1212 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨13, by decide⟩, false), (⟨22, by decide⟩, true), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c98, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false))]
def p1212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 31) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c1179, c98] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1213 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨20, by decide⟩, false), (⟨16, by decide⟩, false), (⟨13, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c100, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 31) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c1179, c100] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1214 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨26, by decide⟩, true), (⟨17, by decide⟩, true), (⟨22, by decide⟩, true), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c102, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1214 : lratChecker f1214 p1214 = .success := by decide +kernel
theorem unsat1214 : Unsatisfiable (PosFin 31) f1214 := by
  apply lratCheckerSound f1214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1214
  · intro a ha; simp [p1214] at ha; subst a; trivial
  · exact checked1214
theorem derived1214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1214 := by
  apply localUnsat_implies_entails f1214 [c1179, c102] c1214 unsat1214 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1215 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨19, by decide⟩, false), (⟨14, by decide⟩, false), (⟨16, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c109, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p1215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1215 : lratChecker f1215 p1215 = .success := by decide +kernel
theorem unsat1215 : Unsatisfiable (PosFin 31) f1215 := by
  apply lratCheckerSound f1215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1215
  · intro a ha; simp [p1215] at ha; subst a; trivial
  · exact checked1215
theorem derived1215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1215 := by
  apply localUnsat_implies_entails f1215 [c1179, c109] c1215 unsat1215 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1216 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨14, by decide⟩, false), (⟨19, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c1179, some c111, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p1216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked1216 : lratChecker f1216 p1216 = .success := by decide +kernel
theorem unsat1216 : Unsatisfiable (PosFin 31) f1216 := by
  apply lratCheckerSound f1216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1216
  · intro a ha; simp [p1216] at ha; subst a; trivial
  · exact checked1216
theorem derived1216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c1216 := by
  apply localUnsat_implies_entails f1216 [c1179, c111] c1216 unsat1216 (by rfl) a
  have h0 : Entails.eval a c1179 := derived1179 a h
  have h1 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
#print axioms derived1216

end CochromaticTwenty.Certificates.Z12Direct_5_8_12
