import MerLeanExperiment.Certificates.B16_0_2Enumerating.Steps0600_0699

/-! Generated from the actual pinned b16_0_2-enumerating-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_2Enumerating
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1114 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1114 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1105, some c109, some c1111, some c67, some c57, some c21, some c110, some c1073, some c1113, some c199, some c184, some c132, some c101, some c261, some c1081, some c263, some c130, some c1089, some c226, some c39, some c253, some c164, some c99, some c16, some c112, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1114 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1114 : lratChecker f1114 p1114 = .success := by decide +kernel
theorem unsat1114 : Unsatisfiable (PosFin 57) f1114 := by
  apply lratCheckerSound f1114 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1114
  · intro a ha; simp [p1114] at ha; subst a; trivial
  · exact checked1114
theorem derived1114 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1114 := by
  apply localUnsat_implies_entails f1114 [c6, c1105, c109, c1111, c67, c57, c21, c110, c1073, c1113, c199, c184, c132, c101, c261, c1081, c263, c130, c1089, c226, c39, c253, c164, c99, c16, c112] c1114 unsat1114 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1105 := derived1105 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c1111 := derived1111 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c110 := h 109 (by decide)
  have h8 : Entails.eval a c1073 := derived1073 a h
  have h9 : Entails.eval a c1113 := derived1113 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c184 := h 183 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c101 := h 100 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c1081 := derived1081 a h
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c130 := h 129 (by decide)
  have h18 : Entails.eval a c1089 := derived1089 a h
  have h19 : Entails.eval a c226 := h 225 (by decide)
  have h20 : Entails.eval a c39 := h 38 (by decide)
  have h21 : Entails.eval a c253 := h 252 (by decide)
  have h22 : Entails.eval a c164 := h 163 (by decide)
  have h23 : Entails.eval a c99 := h 98 (by decide)
  have h24 : Entails.eval a c16 := h 15 (by decide)
  have h25 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1115 : DefaultClause 57 := directClause [(⟨23, by decide⟩, false), (⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1115 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1105, some c109, some c1111, some c67, some c118, some c1114, some c281, some c350, some c21, some c110, some c1073, some c261, some c1081, some c263, some c130, some c1089, some c885, some c28, some c264, some c283, some c220, some c164, some c148, some c16, some c704, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1115 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked1115 : lratChecker f1115 p1115 = .success := by decide +kernel
theorem unsat1115 : Unsatisfiable (PosFin 57) f1115 := by
  apply lratCheckerSound f1115 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1115
  · intro a ha; simp [p1115] at ha; subst a; trivial
  · exact checked1115
theorem derived1115 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1115 := by
  apply localUnsat_implies_entails f1115 [c6, c1105, c109, c1111, c67, c118, c1114, c281, c350, c21, c110, c1073, c261, c1081, c263, c130, c1089, c885, c28, c264, c283, c220, c164, c148, c16, c704] c1115 unsat1115 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1105 := derived1105 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c1111 := derived1111 a h
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c1114 := derived1114 a h
  have h7 : Entails.eval a c281 := h 280 (by decide)
  have h8 : Entails.eval a c350 := h 349 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c1073 := derived1073 a h
  have h12 : Entails.eval a c261 := h 260 (by decide)
  have h13 : Entails.eval a c1081 := derived1081 a h
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c130 := h 129 (by decide)
  have h16 : Entails.eval a c1089 := derived1089 a h
  have h17 : Entails.eval a c885 := derived885 a h
  have h18 : Entails.eval a c28 := h 27 (by decide)
  have h19 : Entails.eval a c264 := h 263 (by decide)
  have h20 : Entails.eval a c283 := h 282 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c164 := h 163 (by decide)
  have h23 : Entails.eval a c148 := h 147 (by decide)
  have h24 : Entails.eval a c16 := h 15 (by decide)
  have h25 : Entails.eval a c704 := derived704 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1116 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨5, by decide⟩, false), (⟨23, by decide⟩, true), (⟨28, by decide⟩, true), (⟨4, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1116 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c36, some c212, some c54, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1116 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1116 : lratChecker f1116 p1116 = .success := by decide +kernel
theorem unsat1116 : Unsatisfiable (PosFin 57) f1116 := by
  apply lratCheckerSound f1116 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1116
  · intro a ha; simp [p1116] at ha; subst a; trivial
  · exact checked1116
theorem derived1116 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1116 := by
  apply localUnsat_implies_entails f1116 [c36, c212, c54] c1116 unsat1116 (by rfl) a
  have h0 : Entails.eval a c36 := h 35 (by decide)
  have h1 : Entails.eval a c212 := h 211 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1117 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1117 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1073, some c1049, some c118, some c6, some c1105, some c759, some c110, some c109, some c1111, some c21, some c57, some c67, some c1114, some c281, some c1115, some c132, some c199, some c197, some c1094, some c17, some c130, some c19, some c248, some c64, some c283, some c140, some c1116, some c267, some c126, some c200, some c991, some c134, some c236, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1117 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked1117 : lratChecker f1117 p1117 = .success := by decide +kernel
theorem unsat1117 : Unsatisfiable (PosFin 57) f1117 := by
  apply lratCheckerSound f1117 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1117
  · intro a ha; simp [p1117] at ha; subst a; trivial
  · exact checked1117
theorem derived1117 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1117 := by
  apply localUnsat_implies_entails f1117 [c1073, c1049, c118, c6, c1105, c759, c110, c109, c1111, c21, c57, c67, c1114, c281, c1115, c132, c199, c197, c1094, c17, c130, c19, c248, c64, c283, c140, c1116, c267, c126, c200, c991, c134, c236] c1117 unsat1117 (by rfl) a
  have h0 : Entails.eval a c1073 := derived1073 a h
  have h1 : Entails.eval a c1049 := derived1049 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c1105 := derived1105 a h
  have h5 : Entails.eval a c759 := derived759 a h
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c1111 := derived1111 a h
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c1114 := derived1114 a h
  have h13 : Entails.eval a c281 := h 280 (by decide)
  have h14 : Entails.eval a c1115 := derived1115 a h
  have h15 : Entails.eval a c132 := h 131 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c197 := h 196 (by decide)
  have h18 : Entails.eval a c1094 := derived1094 a h
  have h19 : Entails.eval a c17 := h 16 (by decide)
  have h20 : Entails.eval a c130 := h 129 (by decide)
  have h21 : Entails.eval a c19 := h 18 (by decide)
  have h22 : Entails.eval a c248 := h 247 (by decide)
  have h23 : Entails.eval a c64 := h 63 (by decide)
  have h24 : Entails.eval a c283 := h 282 (by decide)
  have h25 : Entails.eval a c140 := h 139 (by decide)
  have h26 : Entails.eval a c1116 := derived1116 a h
  have h27 : Entails.eval a c267 := h 266 (by decide)
  have h28 : Entails.eval a c126 := h 125 (by decide)
  have h29 : Entails.eval a c200 := h 199 (by decide)
  have h30 : Entails.eval a c991 := derived991 a h
  have h31 : Entails.eval a c134 := h 133 (by decide)
  have h32 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1118 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨10, by decide⟩, true), (⟨27, by decide⟩, true), (⟨3, by decide⟩, false), (⟨17, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1118 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c118, some c1117, some c42, some c759, some c134, some c83, some c81, some c1053, some c286, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1118 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1118 : lratChecker f1118 p1118 = .success := by decide +kernel
theorem unsat1118 : Unsatisfiable (PosFin 57) f1118 := by
  apply lratCheckerSound f1118 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1118
  · intro a ha; simp [p1118] at ha; subst a; trivial
  · exact checked1118
theorem derived1118 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1118 := by
  apply localUnsat_implies_entails f1118 [c6, c118, c1117, c42, c759, c134, c83, c81, c1053, c286] c1118 unsat1118 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c759 := derived759 a h
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c83 := h 82 (by decide)
  have h7 : Entails.eval a c81 := h 80 (by decide)
  have h8 : Entails.eval a c1053 := derived1053 a h
  have h9 : Entails.eval a c286 := h 285 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1119 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨18, by decide⟩, false), (⟨4, by decide⟩, true), (⟨20, by decide⟩, false), (⟨24, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1119 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c252, some c250, some c101, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1119 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1119 : lratChecker f1119 p1119 = .success := by decide +kernel
theorem unsat1119 : Unsatisfiable (PosFin 57) f1119 := by
  apply lratCheckerSound f1119 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1119
  · intro a ha; simp [p1119] at ha; subst a; trivial
  · exact checked1119
theorem derived1119 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1119 := by
  apply localUnsat_implies_entails f1119 [c252, c250, c101] c1119 unsat1119 (by rfl) a
  have h0 : Entails.eval a c252 := h 251 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1120 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1120 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c132, some c1073, some c1117, some c199, some c6, some c106, some c197, some c19, some c105, some c27, some c155, some c118, some c1094, some c1049, some c126, some c163, some c218, some c23, some c1024, some c50, some c111, some c17, some c200, some c991, some c1118, some c1119, some c97, some c183, some c191, some c335, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1120 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1120 : lratChecker f1120 p1120 = .success := by decide +kernel
theorem unsat1120 : Unsatisfiable (PosFin 57) f1120 := by
  apply lratCheckerSound f1120 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1120
  · intro a ha; simp [p1120] at ha; subst a; trivial
  · exact checked1120
theorem derived1120 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1120 := by
  apply localUnsat_implies_entails f1120 [c132, c1073, c1117, c199, c6, c106, c197, c19, c105, c27, c155, c118, c1094, c1049, c126, c163, c218, c23, c1024, c50, c111, c17, c200, c991, c1118, c1119, c97, c183, c191, c335] c1120 unsat1120 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c1073 := derived1073 a h
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c19 := h 18 (by decide)
  have h8 : Entails.eval a c105 := h 104 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c155 := h 154 (by decide)
  have h11 : Entails.eval a c118 := h 117 (by decide)
  have h12 : Entails.eval a c1094 := derived1094 a h
  have h13 : Entails.eval a c1049 := derived1049 a h
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c218 := h 217 (by decide)
  have h17 : Entails.eval a c23 := h 22 (by decide)
  have h18 : Entails.eval a c1024 := derived1024 a h
  have h19 : Entails.eval a c50 := h 49 (by decide)
  have h20 : Entails.eval a c111 := h 110 (by decide)
  have h21 : Entails.eval a c17 := h 16 (by decide)
  have h22 : Entails.eval a c200 := h 199 (by decide)
  have h23 : Entails.eval a c991 := derived991 a h
  have h24 : Entails.eval a c1118 := derived1118 a h
  have h25 : Entails.eval a c1119 := derived1119 a h
  have h26 : Entails.eval a c97 := h 96 (by decide)
  have h27 : Entails.eval a c183 := h 182 (by decide)
  have h28 : Entails.eval a c191 := h 190 (by decide)
  have h29 : Entails.eval a c335 := h 334 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1121 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1121 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1117, some c106, some c1073, some c132, some c199, some c197, some c130, some c19, some c105, some c27, some c1120, some c267, some c1024, some c36, some c15, some c109, some c163, some c33, some c59, some c249, some c191, some c97, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1121 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1121 : lratChecker f1121 p1121 = .success := by decide +kernel
theorem unsat1121 : Unsatisfiable (PosFin 57) f1121 := by
  apply lratCheckerSound f1121 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1121
  · intro a ha; simp [p1121] at ha; subst a; trivial
  · exact checked1121
theorem derived1121 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1121 := by
  apply localUnsat_implies_entails f1121 [c6, c1117, c106, c1073, c132, c199, c197, c130, c19, c105, c27, c1120, c267, c1024, c36, c15, c109, c163, c33, c59, c249, c191, c97] c1121 unsat1121 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1117 := derived1117 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1073 := derived1073 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c130 := h 129 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c27 := h 26 (by decide)
  have h11 : Entails.eval a c1120 := derived1120 a h
  have h12 : Entails.eval a c267 := h 266 (by decide)
  have h13 : Entails.eval a c1024 := derived1024 a h
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c109 := h 108 (by decide)
  have h17 : Entails.eval a c163 := h 162 (by decide)
  have h18 : Entails.eval a c33 := h 32 (by decide)
  have h19 : Entails.eval a c59 := h 58 (by decide)
  have h20 : Entails.eval a c249 := h 248 (by decide)
  have h21 : Entails.eval a c191 := h 190 (by decide)
  have h22 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1122 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1122 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1121, some c6, some c118, some c1117, some c42, some c106, some c207, some c261, some c263, some c1085, some c28, some c283, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1122 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1122 : lratChecker f1122 p1122 = .success := by decide +kernel
theorem unsat1122 : Unsatisfiable (PosFin 57) f1122 := by
  apply lratCheckerSound f1122 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1122
  · intro a ha; simp [p1122] at ha; subst a; trivial
  · exact checked1122
theorem derived1122 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1122 := by
  apply localUnsat_implies_entails f1122 [c1121, c6, c118, c1117, c42, c106, c207, c261, c263, c1085, c28, c283] c1122 unsat1122 (by rfl) a
  have h0 : Entails.eval a c1121 := derived1121 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c1085 := derived1085 a h
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c283 := h 282 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1123 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨10, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, false), (⟨2, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1123 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1117, some c106, some c1088, some c982, some c264, some c22, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1123 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1123 : lratChecker f1123 p1123 = .success := by decide +kernel
theorem unsat1123 : Unsatisfiable (PosFin 57) f1123 := by
  apply lratCheckerSound f1123 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1123
  · intro a ha; simp [p1123] at ha; subst a; trivial
  · exact checked1123
theorem derived1123 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1123 := by
  apply localUnsat_implies_entails f1123 [c6, c1117, c106, c1088, c982, c264, c22] c1123 unsat1123 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1117 := derived1117 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1088 := derived1088 a h
  have h4 : Entails.eval a c982 := derived982 a h
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1124 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨38, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1124 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c205, some c275, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p1124 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1124 : lratChecker f1124 p1124 = .success := by decide +kernel
theorem unsat1124 : Unsatisfiable (PosFin 57) f1124 := by
  apply lratCheckerSound f1124 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1124
  · intro a ha; simp [p1124] at ha; subst a; trivial
  · exact checked1124
theorem derived1124 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1124 := by
  apply localUnsat_implies_entails f1124 [c22, c205, c275] c1124 unsat1124 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c205 := h 204 (by decide)
  have h2 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1125 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨28, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1125 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1122, some c1121, some c6, some c118, some c1117, some c42, some c1073, some c1049, some c130, some c197, some c13, some c1123, some c263, some c1124, some c777, some c126, some c206, some c699, some c319, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1125 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1125 : lratChecker f1125 p1125 = .success := by decide +kernel
theorem unsat1125 : Unsatisfiable (PosFin 57) f1125 := by
  apply lratCheckerSound f1125 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1125
  · intro a ha; simp [p1125] at ha; subst a; trivial
  · exact checked1125
theorem derived1125 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1125 := by
  apply localUnsat_implies_entails f1125 [c1122, c1121, c6, c118, c1117, c42, c1073, c1049, c130, c197, c13, c1123, c263, c1124, c777, c126, c206, c699, c319] c1125 unsat1125 (by rfl) a
  have h0 : Entails.eval a c1122 := derived1122 a h
  have h1 : Entails.eval a c1121 := derived1121 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c1117 := derived1117 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c1073 := derived1073 a h
  have h7 : Entails.eval a c1049 := derived1049 a h
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c197 := h 196 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c1123 := derived1123 a h
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c1124 := derived1124 a h
  have h14 : Entails.eval a c777 := derived777 a h
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c699 := derived699 a h
  have h18 : Entails.eval a c319 := h 318 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1126 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, false), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1126 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c715, some c200, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p1126 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1126 : lratChecker f1126 p1126 = .success := by decide +kernel
theorem unsat1126 : Unsatisfiable (PosFin 57) f1126 := by
  apply lratCheckerSound f1126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1126
  · intro a ha; simp [p1126] at ha; subst a; trivial
  · exact checked1126
theorem derived1126 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1126 := by
  apply localUnsat_implies_entails f1126 [c13, c715, c200] c1126 unsat1126 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c715 := derived715 a h
  have h2 : Entails.eval a c200 := h 199 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1127 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨3, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1127 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1121, some c6, some c118, some c1117, some c42, some c106, some c1049, some c261, some c268, some c126, some c35, some c23, some c206, some c1126, some c163, some c63, some c69, some c260, some c351, some c64, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1127 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1127 : lratChecker f1127 p1127 = .success := by decide +kernel
theorem unsat1127 : Unsatisfiable (PosFin 57) f1127 := by
  apply lratCheckerSound f1127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1127
  · intro a ha; simp [p1127] at ha; subst a; trivial
  · exact checked1127
theorem derived1127 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1127 := by
  apply localUnsat_implies_entails f1127 [c1121, c6, c118, c1117, c42, c106, c1049, c261, c268, c126, c35, c23, c206, c1126, c163, c63, c69, c260, c351, c64] c1127 unsat1127 (by rfl) a
  have h0 : Entails.eval a c1121 := derived1121 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c261 := h 260 (by decide)
  have h8 : Entails.eval a c268 := h 267 (by decide)
  have h9 : Entails.eval a c126 := h 125 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c1126 := derived1126 a h
  have h14 : Entails.eval a c163 := h 162 (by decide)
  have h15 : Entails.eval a c63 := h 62 (by decide)
  have h16 : Entails.eval a c69 := h 68 (by decide)
  have h17 : Entails.eval a c260 := h 259 (by decide)
  have h18 : Entails.eval a c351 := h 350 (by decide)
  have h19 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1128 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨2, by decide⟩, true), (⟨7, by decide⟩, true), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1128 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1117, some c106, some c1073, some c1049, some c118, some c130, some c1125, some c197, some c53, some c318, some c281, some c16, some c13, some c73, some c60, some c203, some c186, some c283, some c147, some c501, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1128 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1128 : lratChecker f1128 p1128 = .success := by decide +kernel
theorem unsat1128 : Unsatisfiable (PosFin 57) f1128 := by
  apply lratCheckerSound f1128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1128
  · intro a ha; simp [p1128] at ha; subst a; trivial
  · exact checked1128
theorem derived1128 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1128 := by
  apply localUnsat_implies_entails f1128 [c6, c1117, c106, c1073, c1049, c118, c130, c1125, c197, c53, c318, c281, c16, c13, c73, c60, c203, c186, c283, c147, c501] c1128 unsat1128 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1117 := derived1117 a h
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c1073 := derived1073 a h
  have h4 : Entails.eval a c1049 := derived1049 a h
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c1125 := derived1125 a h
  have h8 : Entails.eval a c197 := h 196 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c318 := h 317 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c13 := h 12 (by decide)
  have h14 : Entails.eval a c73 := h 72 (by decide)
  have h15 : Entails.eval a c60 := h 59 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  have h17 : Entails.eval a c186 := h 185 (by decide)
  have h18 : Entails.eval a c283 := h 282 (by decide)
  have h19 : Entails.eval a c147 := h 146 (by decide)
  have h20 : Entails.eval a c501 := derived501 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1129 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1129 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1117, some c105, some c1121, some c6, some c118, some c42, some c1049, some c1128, some c261, some c268, some c1127, some c206, some c50, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1129 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1129 : lratChecker f1129 p1129 = .success := by decide +kernel
theorem unsat1129 : Unsatisfiable (PosFin 57) f1129 := by
  apply lratCheckerSound f1129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1129
  · intro a ha; simp [p1129] at ha; subst a; trivial
  · exact checked1129
theorem derived1129 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1129 := by
  apply localUnsat_implies_entails f1129 [c1117, c105, c1121, c6, c118, c42, c1049, c1128, c261, c268, c1127, c206, c50] c1129 unsat1129 (by rfl) a
  have h0 : Entails.eval a c1117 := derived1117 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c1121 := derived1121 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c1049 := derived1049 a h
  have h7 : Entails.eval a c1128 := derived1128 a h
  have h8 : Entails.eval a c261 := h 260 (by decide)
  have h9 : Entails.eval a c268 := h 267 (by decide)
  have h10 : Entails.eval a c1127 := derived1127 a h
  have h11 : Entails.eval a c206 := h 205 (by decide)
  have h12 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1130 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, false), (⟨4, by decide⟩, true), (⟨26, by decide⟩, true), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1130 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1049, some c319, some c318, some c1121, some c6, some c1117, some c106, some c1073, some c126, some c23, some c699, some c935, some c199, some c163, some c17, some c72, some c161, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1130 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1130 : lratChecker f1130 p1130 = .success := by decide +kernel
theorem unsat1130 : Unsatisfiable (PosFin 57) f1130 := by
  apply lratCheckerSound f1130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1130
  · intro a ha; simp [p1130] at ha; subst a; trivial
  · exact checked1130
theorem derived1130 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1130 := by
  apply localUnsat_implies_entails f1130 [c1049, c319, c318, c1121, c6, c1117, c106, c1073, c126, c23, c699, c935, c199, c163, c17, c72, c161] c1130 unsat1130 (by rfl) a
  have h0 : Entails.eval a c1049 := derived1049 a h
  have h1 : Entails.eval a c319 := h 318 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c1121 := derived1121 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c1117 := derived1117 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c1073 := derived1073 a h
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c699 := derived699 a h
  have h11 : Entails.eval a c935 := derived935 a h
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c163 := h 162 (by decide)
  have h14 : Entails.eval a c17 := h 16 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1131 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1131 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1129, some c109, some c759, some c1117, some c105, some c1121, some c118, some c42, some c1073, some c1049, some c318, some c319, some c50, some c1122, some c1130, some c267, some c264, some c130, some c205, some c197, some c699, some c139, some c231, some c239, some c285, some c174, some c83, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1131 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1131 : lratChecker f1131 p1131 = .success := by decide +kernel
theorem unsat1131 : Unsatisfiable (PosFin 57) f1131 := by
  apply lratCheckerSound f1131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1131
  · intro a ha; simp [p1131] at ha; subst a; trivial
  · exact checked1131
theorem derived1131 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1131 := by
  apply localUnsat_implies_entails f1131 [c6, c1129, c109, c759, c1117, c105, c1121, c118, c42, c1073, c1049, c318, c319, c50, c1122, c1130, c267, c264, c130, c205, c197, c699, c139, c231, c239, c285, c174, c83] c1131 unsat1131 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1129 := derived1129 a h
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c759 := derived759 a h
  have h4 : Entails.eval a c1117 := derived1117 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c1121 := derived1121 a h
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c1073 := derived1073 a h
  have h10 : Entails.eval a c1049 := derived1049 a h
  have h11 : Entails.eval a c318 := h 317 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c50 := h 49 (by decide)
  have h14 : Entails.eval a c1122 := derived1122 a h
  have h15 : Entails.eval a c1130 := derived1130 a h
  have h16 : Entails.eval a c267 := h 266 (by decide)
  have h17 : Entails.eval a c264 := h 263 (by decide)
  have h18 : Entails.eval a c130 := h 129 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  have h20 : Entails.eval a c197 := h 196 (by decide)
  have h21 : Entails.eval a c699 := derived699 a h
  have h22 : Entails.eval a c139 := h 138 (by decide)
  have h23 : Entails.eval a c231 := h 230 (by decide)
  have h24 : Entails.eval a c239 := h 238 (by decide)
  have h25 : Entails.eval a c285 := h 284 (by decide)
  have h26 : Entails.eval a c174 := h 173 (by decide)
  have h27 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1132 : DefaultClause 57 := directClause [(⟨46, by decide⟩, false), (⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨25, by decide⟩, true), (⟨1, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1132 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c78, some c83, some c285, some (DefaultClause.unit (⟨46, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1132 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1132 : lratChecker f1132 p1132 = .success := by decide +kernel
theorem unsat1132 : Unsatisfiable (PosFin 57) f1132 := by
  apply lratCheckerSound f1132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1132
  · intro a ha; simp [p1132] at ha; subst a; trivial
  · exact checked1132
theorem derived1132 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1132 := by
  apply localUnsat_implies_entails f1132 [c78, c83, c285] c1132 unsat1132 (by rfl) a
  have h0 : Entails.eval a c78 := h 77 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c285 := h 284 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1133 : DefaultClause 57 := directClause [(⟨42, by decide⟩, true), (⟨47, by decide⟩, false), (⟨12, by decide⟩, false), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1133 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c285, some c134, some c231, some c200, some c206, some c135, some c239, some (DefaultClause.unit (⟨42, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p1133 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1133 : lratChecker f1133 p1133 = .success := by decide +kernel
theorem unsat1133 : Unsatisfiable (PosFin 57) f1133 := by
  apply lratCheckerSound f1133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1133
  · intro a ha; simp [p1133] at ha; subst a; trivial
  · exact checked1133
theorem derived1133 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1133 := by
  apply localUnsat_implies_entails f1133 [c285, c134, c231, c200, c206, c135, c239] c1133 unsat1133 (by rfl) a
  have h0 : Entails.eval a c285 := h 284 (by decide)
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c206 := h 205 (by decide)
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c239 := h 238 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1134 : DefaultClause 57 := directClause [(⟨41, by decide⟩, false), (⟨47, by decide⟩, false), (⟨12, by decide⟩, false), (⟨46, by decide⟩, true), (⟨27, by decide⟩, true), (⟨26, by decide⟩, true), (⟨2, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨6, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1134 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1133, some c366, some c231, some c178, some c205, some c206, some c203, some c1011, some (DefaultClause.unit (⟨41, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p1134 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1134 : lratChecker f1134 p1134 = .success := by decide +kernel
theorem unsat1134 : Unsatisfiable (PosFin 57) f1134 := by
  apply lratCheckerSound f1134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1134
  · intro a ha; simp [p1134] at ha; subst a; trivial
  · exact checked1134
theorem derived1134 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1134 := by
  apply localUnsat_implies_entails f1134 [c1133, c366, c231, c178, c205, c206, c203, c1011] c1134 unsat1134 (by rfl) a
  have h0 : Entails.eval a c1133 := derived1133 a h
  have h1 : Entails.eval a c366 := h 365 (by decide)
  have h2 : Entails.eval a c231 := h 230 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c205 := h 204 (by decide)
  have h5 : Entails.eval a c206 := h 205 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c1011 := derived1011 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1135 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨27, by decide⟩, true), (⟨2, by decide⟩, false), (⟨7, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1135 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c1117, some c118, some c42, some c759, some c1132, some c109, some c1121, some c16, some c180, some c1134, some c286, some c239, some c373, some c126, some c178, some c203, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1135 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1135 : lratChecker f1135 p1135 = .success := by decide +kernel
theorem unsat1135 : Unsatisfiable (PosFin 57) f1135 := by
  apply lratCheckerSound f1135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1135
  · intro a ha; simp [p1135] at ha; subst a; trivial
  · exact checked1135
theorem derived1135 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1135 := by
  apply localUnsat_implies_entails f1135 [c6, c1117, c118, c42, c759, c1132, c109, c1121, c16, c180, c1134, c286, c239, c373, c126, c178, c203] c1135 unsat1135 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c1117 := derived1117 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c759 := derived759 a h
  have h5 : Entails.eval a c1132 := derived1132 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c1121 := derived1121 a h
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c180 := h 179 (by decide)
  have h10 : Entails.eval a c1134 := derived1134 a h
  have h11 : Entails.eval a c286 := h 285 (by decide)
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c373 := h 372 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c178 := h 177 (by decide)
  have h16 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1136 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1136 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1121, some c6, some c118, some c1117, some c42, some c1073, some c105, some c1129, some c1131, some c1135, some c199, some c197, some c1094, some c130, some c263, some c268, some c206, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1136 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1136 : lratChecker f1136 p1136 = .success := by decide +kernel
theorem unsat1136 : Unsatisfiable (PosFin 57) f1136 := by
  apply lratCheckerSound f1136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1136
  · intro a ha; simp [p1136] at ha; subst a; trivial
  · exact checked1136
theorem derived1136 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1136 := by
  apply localUnsat_implies_entails f1136 [c1121, c6, c118, c1117, c42, c1073, c105, c1129, c1131, c1135, c199, c197, c1094, c130, c263, c268, c206] c1136 unsat1136 (by rfl) a
  have h0 : Entails.eval a c1121 := derived1121 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c1073 := derived1073 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1129 := derived1129 a h
  have h8 : Entails.eval a c1131 := derived1131 a h
  have h9 : Entails.eval a c1135 := derived1135 a h
  have h10 : Entails.eval a c199 := h 198 (by decide)
  have h11 : Entails.eval a c197 := h 196 (by decide)
  have h12 : Entails.eval a c1094 := derived1094 a h
  have h13 : Entails.eval a c130 := h 129 (by decide)
  have h14 : Entails.eval a c263 := h 262 (by decide)
  have h15 : Entails.eval a c268 := h 267 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1137 : DefaultClause 57 := directClause [(⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨8, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1137 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c199, some c197, some c19, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p1137 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1137 : lratChecker f1137 p1137 = .success := by decide +kernel
theorem unsat1137 : Unsatisfiable (PosFin 57) f1137 := by
  apply lratCheckerSound f1137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1137
  · intro a ha; simp [p1137] at ha; subst a; trivial
  · exact checked1137
theorem derived1137 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1137 := by
  apply localUnsat_implies_entails f1137 [c199, c197, c19] c1137 unsat1137 (by rfl) a
  have h0 : Entails.eval a c199 := h 198 (by decide)
  have h1 : Entails.eval a c197 := h 196 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1138 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨47, by decide⟩, false), (⟨46, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1138 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1121, some c130, some c178, some c242, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨47, by decide⟩, true)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1138 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1138 : lratChecker f1138 p1138 = .success := by decide +kernel
theorem unsat1138 : Unsatisfiable (PosFin 57) f1138 := by
  apply lratCheckerSound f1138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1138
  · intro a ha; simp [p1138] at ha; subst a; trivial
  · exact checked1138
theorem derived1138 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1138 := by
  apply localUnsat_implies_entails f1138 [c1121, c130, c178, c242] c1138 unsat1138 (by rfl) a
  have h0 : Entails.eval a c1121 := derived1121 a h
  have h1 : Entails.eval a c130 := h 129 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1139 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1139 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1121, some c6, some c118, some c1117, some c42, some c1049, some c261, some c268, some c126, some c206, some c203, some c715, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1139 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1139 : lratChecker f1139 p1139 = .success := by decide +kernel
theorem unsat1139 : Unsatisfiable (PosFin 57) f1139 := by
  apply lratCheckerSound f1139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1139
  · intro a ha; simp [p1139] at ha; subst a; trivial
  · exact checked1139
theorem derived1139 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1139 := by
  apply localUnsat_implies_entails f1139 [c1121, c6, c118, c1117, c42, c1049, c261, c268, c126, c206, c203, c715] c1139 unsat1139 (by rfl) a
  have h0 : Entails.eval a c1121 := derived1121 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c1049 := derived1049 a h
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c268 := h 267 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  have h10 : Entails.eval a c203 := h 202 (by decide)
  have h11 : Entails.eval a c715 := derived715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1140 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1140 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1073, some c6, some c1117, some c106, some c1137, some c1121, some c118, some c42, some c759, some c1132, some c180, some c1138, some c1139, some c25, some c39, some c263, some c940, some c1036, some c126, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1140 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1140 : lratChecker f1140 p1140 = .success := by decide +kernel
theorem unsat1140 : Unsatisfiable (PosFin 57) f1140 := by
  apply lratCheckerSound f1140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1140
  · intro a ha; simp [p1140] at ha; subst a; trivial
  · exact checked1140
theorem derived1140 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1140 := by
  apply localUnsat_implies_entails f1140 [c1073, c6, c1117, c106, c1137, c1121, c118, c42, c759, c1132, c180, c1138, c1139, c25, c39, c263, c940, c1036, c126] c1140 unsat1140 (by rfl) a
  have h0 : Entails.eval a c1073 := derived1073 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c106 := h 105 (by decide)
  have h4 : Entails.eval a c1137 := derived1137 a h
  have h5 : Entails.eval a c1121 := derived1121 a h
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c759 := derived759 a h
  have h9 : Entails.eval a c1132 := derived1132 a h
  have h10 : Entails.eval a c180 := h 179 (by decide)
  have h11 : Entails.eval a c1138 := derived1138 a h
  have h12 : Entails.eval a c1139 := derived1139 a h
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c39 := h 38 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c940 := derived940 a h
  have h17 : Entails.eval a c1036 := derived1036 a h
  have h18 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1141 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1141 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1140, some c1073, some c6, some c1117, some c106, some c1137, some c1121, some c1139, some c25, some c39, some c32, some c263, some c777, some c1036, some c126, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1141 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1141 : lratChecker f1141 p1141 = .success := by decide +kernel
theorem unsat1141 : Unsatisfiable (PosFin 57) f1141 := by
  apply lratCheckerSound f1141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1141
  · intro a ha; simp [p1141] at ha; subst a; trivial
  · exact checked1141
theorem derived1141 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1141 := by
  apply localUnsat_implies_entails f1141 [c1140, c1073, c6, c1117, c106, c1137, c1121, c1139, c25, c39, c32, c263, c777, c1036, c126] c1141 unsat1141 (by rfl) a
  have h0 : Entails.eval a c1140 := derived1140 a h
  have h1 : Entails.eval a c1073 := derived1073 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c106 := h 105 (by decide)
  have h5 : Entails.eval a c1137 := derived1137 a h
  have h6 : Entails.eval a c1121 := derived1121 a h
  have h7 : Entails.eval a c1139 := derived1139 a h
  have h8 : Entails.eval a c25 := h 24 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c263 := h 262 (by decide)
  have h12 : Entails.eval a c777 := derived777 a h
  have h13 : Entails.eval a c1036 := derived1036 a h
  have h14 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1142 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1142 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1121, some c6, some c118, some c1117, some c42, some c106, some c1073, some c1049, some c1137, some c1140, some c1141, some c130, some c12, some c261, some c268, some c126, some c206, some c200, some c715, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1142 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1142 : lratChecker f1142 p1142 = .success := by decide +kernel
theorem unsat1142 : Unsatisfiable (PosFin 57) f1142 := by
  apply lratCheckerSound f1142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1142
  · intro a ha; simp [p1142] at ha; subst a; trivial
  · exact checked1142
theorem derived1142 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1142 := by
  apply localUnsat_implies_entails f1142 [c1121, c6, c118, c1117, c42, c106, c1073, c1049, c1137, c1140, c1141, c130, c12, c261, c268, c126, c206, c200, c715] c1142 unsat1142 (by rfl) a
  have h0 : Entails.eval a c1121 := derived1121 a h
  have h1 : Entails.eval a c6 := h 5 (by decide)
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c1117 := derived1117 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c1073 := derived1073 a h
  have h7 : Entails.eval a c1049 := derived1049 a h
  have h8 : Entails.eval a c1137 := derived1137 a h
  have h9 : Entails.eval a c1140 := derived1140 a h
  have h10 : Entails.eval a c1141 := derived1141 a h
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c12 := h 11 (by decide)
  have h13 : Entails.eval a c261 := h 260 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c715 := derived715 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1143 : DefaultClause 57 := directClause [(⟨13, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1143 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1117, some c1142, some c105, some c1121, some c6, some c118, some c42, some c1049, some c130, some c261, some c268, some c126, some c206, some c319, some c1126, some c935, some c759, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1143 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1143 : lratChecker f1143 p1143 = .success := by decide +kernel
theorem unsat1143 : Unsatisfiable (PosFin 57) f1143 := by
  apply lratCheckerSound f1143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1143
  · intro a ha; simp [p1143] at ha; subst a; trivial
  · exact checked1143
theorem derived1143 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1143 := by
  apply localUnsat_implies_entails f1143 [c1117, c1142, c105, c1121, c6, c118, c42, c1049, c130, c261, c268, c126, c206, c319, c1126, c935, c759] c1143 unsat1143 (by rfl) a
  have h0 : Entails.eval a c1117 := derived1117 a h
  have h1 : Entails.eval a c1142 := derived1142 a h
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c1121 := derived1121 a h
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c1049 := derived1049 a h
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c268 := h 267 (by decide)
  have h11 : Entails.eval a c126 := h 125 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c319 := h 318 (by decide)
  have h14 : Entails.eval a c1126 := derived1126 a h
  have h15 : Entails.eval a c935 := derived935 a h
  have h16 : Entails.eval a c759 := derived759 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1144 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨19, by decide⟩, false), (⟨37, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, true), (⟨7, by decide⟩, true), (⟨5, by decide⟩, false), (⟨23, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1144 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c203, some c162, some c16, some c53, some c111, some c699, some c59, some c282, some c255, some c63, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1144 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1144 : lratChecker f1144 p1144 = .success := by decide +kernel
theorem unsat1144 : Unsatisfiable (PosFin 57) f1144 := by
  apply lratCheckerSound f1144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1144
  · intro a ha; simp [p1144] at ha; subst a; trivial
  · exact checked1144
theorem derived1144 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1144 := by
  apply localUnsat_implies_entails f1144 [c203, c162, c16, c53, c111, c699, c59, c282, c255, c63] c1144 unsat1144 (by rfl) a
  have h0 : Entails.eval a c203 := h 202 (by decide)
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c53 := h 52 (by decide)
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c699 := derived699 a h
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c282 := h 281 (by decide)
  have h8 : Entails.eval a c255 := h 254 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1145 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1145 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c118, some c1049, some c1121, some c1142, some c1117, some c105, some c1143, some c1136, some c1139, some c226, some c1018, some c1144, some c42, some c106, some c1073, some c319, some c282, some c1135, some c63, some c69, some c13, some c982, some c940, some c260, some c317, some c64, some c147, some c160, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1145 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1145 : lratChecker f1145 p1145 = .success := by decide +kernel
theorem unsat1145 : Unsatisfiable (PosFin 57) f1145 := by
  apply lratCheckerSound f1145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1145
  · intro a ha; simp [p1145] at ha; subst a; trivial
  · exact checked1145
theorem derived1145 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1145 := by
  apply localUnsat_implies_entails f1145 [c6, c118, c1049, c1121, c1142, c1117, c105, c1143, c1136, c1139, c226, c1018, c1144, c42, c106, c1073, c319, c282, c1135, c63, c69, c13, c982, c940, c260, c317, c64, c147, c160] c1145 unsat1145 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c1121 := derived1121 a h
  have h4 : Entails.eval a c1142 := derived1142 a h
  have h5 : Entails.eval a c1117 := derived1117 a h
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c1143 := derived1143 a h
  have h8 : Entails.eval a c1136 := derived1136 a h
  have h9 : Entails.eval a c1139 := derived1139 a h
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c1018 := derived1018 a h
  have h12 : Entails.eval a c1144 := derived1144 a h
  have h13 : Entails.eval a c42 := h 41 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c1073 := derived1073 a h
  have h16 : Entails.eval a c319 := h 318 (by decide)
  have h17 : Entails.eval a c282 := h 281 (by decide)
  have h18 : Entails.eval a c1135 := derived1135 a h
  have h19 : Entails.eval a c63 := h 62 (by decide)
  have h20 : Entails.eval a c69 := h 68 (by decide)
  have h21 : Entails.eval a c13 := h 12 (by decide)
  have h22 : Entails.eval a c982 := derived982 a h
  have h23 : Entails.eval a c940 := derived940 a h
  have h24 : Entails.eval a c260 := h 259 (by decide)
  have h25 : Entails.eval a c317 := h 316 (by decide)
  have h26 : Entails.eval a c64 := h 63 (by decide)
  have h27 : Entails.eval a c147 := h 146 (by decide)
  have h28 : Entails.eval a c160 := h 159 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1146 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1146 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1142, some c1136, some c1117, some c105, some c1121, some c6, some c118, some c42, some c1049, some c1143, some c1139, some c226, some c1018, some c1144, some c1145, some c139, some c239, some c174, some c135, some c78, some c318, some c50, some c715, some c278, some c287, some c59, some c164, some c89, some c60, some c24, some c253, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1146 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1146 : lratChecker f1146 p1146 = .success := by decide +kernel
theorem unsat1146 : Unsatisfiable (PosFin 57) f1146 := by
  apply lratCheckerSound f1146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1146
  · intro a ha; simp [p1146] at ha; subst a; trivial
  · exact checked1146
theorem derived1146 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1146 := by
  apply localUnsat_implies_entails f1146 [c1142, c1136, c1117, c105, c1121, c6, c118, c42, c1049, c1143, c1139, c226, c1018, c1144, c1145, c139, c239, c174, c135, c78, c318, c50, c715, c278, c287, c59, c164, c89, c60, c24, c253] c1146 unsat1146 (by rfl) a
  have h0 : Entails.eval a c1142 := derived1142 a h
  have h1 : Entails.eval a c1136 := derived1136 a h
  have h2 : Entails.eval a c1117 := derived1117 a h
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c1121 := derived1121 a h
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c118 := h 117 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c1049 := derived1049 a h
  have h9 : Entails.eval a c1143 := derived1143 a h
  have h10 : Entails.eval a c1139 := derived1139 a h
  have h11 : Entails.eval a c226 := h 225 (by decide)
  have h12 : Entails.eval a c1018 := derived1018 a h
  have h13 : Entails.eval a c1144 := derived1144 a h
  have h14 : Entails.eval a c1145 := derived1145 a h
  have h15 : Entails.eval a c139 := h 138 (by decide)
  have h16 : Entails.eval a c239 := h 238 (by decide)
  have h17 : Entails.eval a c174 := h 173 (by decide)
  have h18 : Entails.eval a c135 := h 134 (by decide)
  have h19 : Entails.eval a c78 := h 77 (by decide)
  have h20 : Entails.eval a c318 := h 317 (by decide)
  have h21 : Entails.eval a c50 := h 49 (by decide)
  have h22 : Entails.eval a c715 := derived715 a h
  have h23 : Entails.eval a c278 := h 277 (by decide)
  have h24 : Entails.eval a c287 := h 286 (by decide)
  have h25 : Entails.eval a c59 := h 58 (by decide)
  have h26 : Entails.eval a c164 := h 163 (by decide)
  have h27 : Entails.eval a c89 := h 88 (by decide)
  have h28 : Entails.eval a c60 := h 59 (by decide)
  have h29 : Entails.eval a c24 := h 23 (by decide)
  have h30 : Entails.eval a c253 := h 252 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1147 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1147 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c118, some c1049, some c1073, some c1117, some c106, some c42, some c1121, some c1142, some c105, some c1136, some c1146, some c199, some c197, some c1094, some c130, some c263, some c268, some c126, some c222, some c206, some c163, some c50, some c63, some c191, some c260, some c99, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1147 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1147 : lratChecker f1147 p1147 = .success := by decide +kernel
theorem unsat1147 : Unsatisfiable (PosFin 57) f1147 := by
  apply lratCheckerSound f1147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1147
  · intro a ha; simp [p1147] at ha; subst a; trivial
  · exact checked1147
theorem derived1147 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1147 := by
  apply localUnsat_implies_entails f1147 [c6, c118, c1049, c1073, c1117, c106, c42, c1121, c1142, c105, c1136, c1146, c199, c197, c1094, c130, c263, c268, c126, c222, c206, c163, c50, c63, c191, c260, c99] c1147 unsat1147 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c1049 := derived1049 a h
  have h3 : Entails.eval a c1073 := derived1073 a h
  have h4 : Entails.eval a c1117 := derived1117 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c1121 := derived1121 a h
  have h8 : Entails.eval a c1142 := derived1142 a h
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c1136 := derived1136 a h
  have h11 : Entails.eval a c1146 := derived1146 a h
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  have h14 : Entails.eval a c1094 := derived1094 a h
  have h15 : Entails.eval a c130 := h 129 (by decide)
  have h16 : Entails.eval a c263 := h 262 (by decide)
  have h17 : Entails.eval a c268 := h 267 (by decide)
  have h18 : Entails.eval a c126 := h 125 (by decide)
  have h19 : Entails.eval a c222 := h 221 (by decide)
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c163 := h 162 (by decide)
  have h22 : Entails.eval a c50 := h 49 (by decide)
  have h23 : Entails.eval a c63 := h 62 (by decide)
  have h24 : Entails.eval a c191 := h 190 (by decide)
  have h25 : Entails.eval a c260 := h 259 (by decide)
  have h26 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1148 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨16, by decide⟩, true), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1148 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c34, some c30, some c163, some c1094, some c106, some c63, some c191, some c260, some c99, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1148 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1148 : lratChecker f1148 p1148 = .success := by decide +kernel
theorem unsat1148 : Unsatisfiable (PosFin 57) f1148 := by
  apply lratCheckerSound f1148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1148
  · intro a ha; simp [p1148] at ha; subst a; trivial
  · exact checked1148
theorem derived1148 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1148 := by
  apply localUnsat_implies_entails f1148 [c23, c34, c30, c163, c1094, c106, c63, c191, c260, c99] c1148 unsat1148 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c1094 := derived1094 a h
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c260 := h 259 (by decide)
  have h9 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1149 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨3, by decide⟩, false), (⟨16, by decide⟩, true), (⟨27, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1149 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1092, some c110, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1149 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1149 : lratChecker f1149 p1149 = .success := by decide +kernel
theorem unsat1149 : Unsatisfiable (PosFin 57) f1149 := by
  apply lratCheckerSound f1149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1149
  · intro a ha; simp [p1149] at ha; subst a; trivial
  · exact checked1149
theorem derived1149 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1149 := by
  apply localUnsat_implies_entails f1149 [c1092, c110] c1149 unsat1149 (by rfl) a
  have h0 : Entails.eval a c1092 := derived1092 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1150 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1150 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c261, some c113, some c198, some c1148, some c50, some c1137, some c1149, some c26, some c154, some c218, some c163, some c278, some c63, some c61, some c258, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1150 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1150 : lratChecker f1150 p1150 = .success := by decide +kernel
theorem unsat1150 : Unsatisfiable (PosFin 57) f1150 := by
  apply lratCheckerSound f1150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1150
  · intro a ha; simp [p1150] at ha; subst a; trivial
  · exact checked1150
theorem derived1150 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1150 := by
  apply localUnsat_implies_entails f1150 [c1147, c261, c113, c198, c1148, c50, c1137, c1149, c26, c154, c218, c163, c278, c63, c61, c258] c1150 unsat1150 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c1148 := derived1148 a h
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c1137 := derived1137 a h
  have h7 : Entails.eval a c1149 := derived1149 a h
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c218 := h 217 (by decide)
  have h11 : Entails.eval a c163 := h 162 (by decide)
  have h12 : Entails.eval a c278 := h 277 (by decide)
  have h13 : Entails.eval a c63 := h 62 (by decide)
  have h14 : Entails.eval a c61 := h 60 (by decide)
  have h15 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1151 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, true), (⟨21, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1151 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c198, some c885, some c1148, some c263, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1151 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1151 : lratChecker f1151 p1151 = .success := by decide +kernel
theorem unsat1151 : Unsatisfiable (PosFin 57) f1151 := by
  apply lratCheckerSound f1151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1151
  · intro a ha; simp [p1151] at ha; subst a; trivial
  · exact checked1151
theorem derived1151 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1151 := by
  apply localUnsat_implies_entails f1151 [c1147, c198, c885, c1148, c263] c1151 unsat1151 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c198 := h 197 (by decide)
  have h2 : Entails.eval a c885 := derived885 a h
  have h3 : Entails.eval a c1148 := derived1148 a h
  have h4 : Entails.eval a c263 := h 262 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1152 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1152 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1150, some c5, some c50, some c23, some c34, some c278, some c226, some c1151, some c113, some c263, some c1094, some c227, some c167, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1152 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1152 : lratChecker f1152 p1152 = .success := by decide +kernel
theorem unsat1152 : Unsatisfiable (PosFin 57) f1152 := by
  apply lratCheckerSound f1152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1152
  · intro a ha; simp [p1152] at ha; subst a; trivial
  · exact checked1152
theorem derived1152 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1152 := by
  apply localUnsat_implies_entails f1152 [c1147, c1150, c5, c50, c23, c34, c278, c226, c1151, c113, c263, c1094, c227, c167] c1152 unsat1152 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1150 := derived1150 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c278 := h 277 (by decide)
  have h7 : Entails.eval a c226 := h 225 (by decide)
  have h8 : Entails.eval a c1151 := derived1151 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c263 := h 262 (by decide)
  have h11 : Entails.eval a c1094 := derived1094 a h
  have h12 : Entails.eval a c227 := h 226 (by decide)
  have h13 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1153 : DefaultClause 57 := directClause [(⟨25, by decide⟩, true), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1153 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1152, some c206, some c261, some c263, some c885, some c211, some c131, some c317, some c202, some c141, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1153 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1153 : lratChecker f1153 p1153 = .success := by decide +kernel
theorem unsat1153 : Unsatisfiable (PosFin 57) f1153 := by
  apply lratCheckerSound f1153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1153
  · intro a ha; simp [p1153] at ha; subst a; trivial
  · exact checked1153
theorem derived1153 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1153 := by
  apply localUnsat_implies_entails f1153 [c1147, c1152, c206, c261, c263, c885, c211, c131, c317, c202, c141] c1153 unsat1153 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1152 := derived1152 a h
  have h2 : Entails.eval a c206 := h 205 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c885 := derived885 a h
  have h6 : Entails.eval a c211 := h 210 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c317 := h 316 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1154 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1154 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c42, some c41, some c26, some c34, some c38, some c270, some c218, some c163, some c63, some c258, some c102, some c61, some c298, some c352, some c336, some c72, some c378, some c541, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1154 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1154 : lratChecker f1154 p1154 = .success := by decide +kernel
theorem unsat1154 : Unsatisfiable (PosFin 57) f1154 := by
  apply lratCheckerSound f1154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1154
  · intro a ha; simp [p1154] at ha; subst a; trivial
  · exact checked1154
theorem derived1154 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1154 := by
  apply localUnsat_implies_entails f1154 [c42, c41, c26, c34, c38, c270, c218, c163, c63, c258, c102, c61, c298, c352, c336, c72, c378, c541] c1154 unsat1154 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c41 := h 40 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c270 := h 269 (by decide)
  have h6 : Entails.eval a c218 := h 217 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c258 := h 257 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c298 := h 297 (by decide)
  have h13 : Entails.eval a c352 := h 351 (by decide)
  have h14 : Entails.eval a c336 := h 335 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c378 := h 377 (by decide)
  have h17 : Entails.eval a c541 := derived541 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1155 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1155 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1154, some c1, some c30, some c21, some c963, some c155, some c269, some c222, some c63, some c226, some c258, some c183, some c61, some c343, some c111, some c72, some c95, some c474, some c378, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1155 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1155 : lratChecker f1155 p1155 = .success := by decide +kernel
theorem unsat1155 : Unsatisfiable (PosFin 57) f1155 := by
  apply lratCheckerSound f1155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1155
  · intro a ha; simp [p1155] at ha; subst a; trivial
  · exact checked1155
theorem derived1155 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1155 := by
  apply localUnsat_implies_entails f1155 [c1147, c1154, c1, c30, c21, c963, c155, c269, c222, c63, c226, c258, c183, c61, c343, c111, c72, c95, c474, c378] c1155 unsat1155 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1154 := derived1154 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c269 := h 268 (by decide)
  have h8 : Entails.eval a c222 := h 221 (by decide)
  have h9 : Entails.eval a c63 := h 62 (by decide)
  have h10 : Entails.eval a c226 := h 225 (by decide)
  have h11 : Entails.eval a c258 := h 257 (by decide)
  have h12 : Entails.eval a c183 := h 182 (by decide)
  have h13 : Entails.eval a c61 := h 60 (by decide)
  have h14 : Entails.eval a c343 := h 342 (by decide)
  have h15 : Entails.eval a c111 := h 110 (by decide)
  have h16 : Entails.eval a c72 := h 71 (by decide)
  have h17 : Entails.eval a c95 := h 94 (by decide)
  have h18 : Entails.eval a c474 := derived474 a h
  have h19 : Entails.eval a c378 := h 377 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1156 : DefaultClause 57 := directClause [(⟨30, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1156 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1153, some c313, some c1155, some c261, some c263, some c5, some c885, some c211, some c131, some c41, some c50, some c202, some c34, some c35, some c9, some c110, some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1156 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1156 : lratChecker f1156 p1156 = .success := by decide +kernel
theorem unsat1156 : Unsatisfiable (PosFin 57) f1156 := by
  apply lratCheckerSound f1156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1156
  · intro a ha; simp [p1156] at ha; subst a; trivial
  · exact checked1156
theorem derived1156 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1156 := by
  apply localUnsat_implies_entails f1156 [c1147, c1153, c313, c1155, c261, c263, c5, c885, c211, c131, c41, c50, c202, c34, c35, c9, c110] c1156 unsat1156 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1153 := derived1153 a h
  have h2 : Entails.eval a c313 := h 312 (by decide)
  have h3 : Entails.eval a c1155 := derived1155 a h
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c5 := h 4 (by decide)
  have h7 : Entails.eval a c885 := derived885 a h
  have h8 : Entails.eval a c211 := h 210 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c41 := h 40 (by decide)
  have h11 : Entails.eval a c50 := h 49 (by decide)
  have h12 : Entails.eval a c202 := h 201 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c35 := h 34 (by decide)
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1157 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨9, by decide⟩, true), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1157 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c261, some c263, some c5, some c131, some c50, some c202, some c34, some c35, some c106, some c110, some c9, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1157 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1157 : lratChecker f1157 p1157 = .success := by decide +kernel
theorem unsat1157 : Unsatisfiable (PosFin 57) f1157 := by
  apply lratCheckerSound f1157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1157
  · intro a ha; simp [p1157] at ha; subst a; trivial
  · exact checked1157
theorem derived1157 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1157 := by
  apply localUnsat_implies_entails f1157 [c1147, c261, c263, c5, c131, c50, c202, c34, c35, c106, c110, c9] c1157 unsat1157 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c263 := h 262 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c202 := h 201 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1158 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨24, by decide⟩, true), (⟨1, by decide⟩, false), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1158 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c34, some c35, some c106, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1158 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1158 : lratChecker f1158 p1158 = .success := by decide +kernel
theorem unsat1158 : Unsatisfiable (PosFin 57) f1158 := by
  apply lratCheckerSound f1158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1158
  · intro a ha; simp [p1158] at ha; subst a; trivial
  · exact checked1158
theorem derived1158 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1158 := by
  apply localUnsat_implies_entails f1158 [c34, c35, c106] c1158 unsat1158 (by rfl) a
  have h0 : Entails.eval a c34 := h 33 (by decide)
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1159 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1159 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c278, some c63, some c61, some c258, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1159 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1159 : lratChecker f1159 p1159 = .success := by decide +kernel
theorem unsat1159 : Unsatisfiable (PosFin 57) f1159 := by
  apply lratCheckerSound f1159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1159
  · intro a ha; simp [p1159] at ha; subst a; trivial
  · exact checked1159
theorem derived1159 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1159 := by
  apply localUnsat_implies_entails f1159 [c163, c278, c63, c61, c258] c1159 unsat1159 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c278 := h 277 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1160 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1160 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1156, some c210, some c318, some c1147, some c1157, some c113, some c1, some c41, some c5, some c1159, some c218, some c222, some c23, some c347, some c269, some c61, some c75, some c258, some c305, some c106, some c44, some c104, some c340, some c379, some c195, some c97, some c149, some c108, some c165, some c193, some c60, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1160 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1160 : lratChecker f1160 p1160 = .success := by decide +kernel
theorem unsat1160 : Unsatisfiable (PosFin 57) f1160 := by
  apply lratCheckerSound f1160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1160
  · intro a ha; simp [p1160] at ha; subst a; trivial
  · exact checked1160
theorem derived1160 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1160 := by
  apply localUnsat_implies_entails f1160 [c1156, c210, c318, c1147, c1157, c113, c1, c41, c5, c1159, c218, c222, c23, c347, c269, c61, c75, c258, c305, c106, c44, c104, c340, c379, c195, c97, c149, c108, c165, c193, c60] c1160 unsat1160 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c318 := h 317 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c1157 := derived1157 a h
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c1159 := derived1159 a h
  have h10 : Entails.eval a c218 := h 217 (by decide)
  have h11 : Entails.eval a c222 := h 221 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c347 := h 346 (by decide)
  have h14 : Entails.eval a c269 := h 268 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c305 := h 304 (by decide)
  have h19 : Entails.eval a c106 := h 105 (by decide)
  have h20 : Entails.eval a c44 := h 43 (by decide)
  have h21 : Entails.eval a c104 := h 103 (by decide)
  have h22 : Entails.eval a c340 := h 339 (by decide)
  have h23 : Entails.eval a c379 := h 378 (by decide)
  have h24 : Entails.eval a c195 := h 194 (by decide)
  have h25 : Entails.eval a c97 := h 96 (by decide)
  have h26 : Entails.eval a c149 := h 148 (by decide)
  have h27 : Entails.eval a c108 := h 107 (by decide)
  have h28 : Entails.eval a c165 := h 164 (by decide)
  have h29 : Entails.eval a c193 := h 192 (by decide)
  have h30 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1161 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, false), (⟨19, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1161 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c218, some c222, some c154, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1161 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1161 : lratChecker f1161 p1161 = .success := by decide +kernel
theorem unsat1161 : Unsatisfiable (PosFin 57) f1161 := by
  apply lratCheckerSound f1161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1161
  · intro a ha; simp [p1161] at ha; subst a; trivial
  · exact checked1161
theorem derived1161 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1161 := by
  apply localUnsat_implies_entails f1161 [c1147, c218, c222, c154] c1161 unsat1161 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c218 := h 217 (by decide)
  have h2 : Entails.eval a c222 := h 221 (by decide)
  have h3 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1162 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨1, by decide⟩, false), (⟨9, by decide⟩, false), (⟨27, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1162 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c261, some c1161, some c163, some c1159, some c63, some c50, some c191, some c34, some c1158, some c106, some c260, some c99, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1162 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1162 : lratChecker f1162 p1162 = .success := by decide +kernel
theorem unsat1162 : Unsatisfiable (PosFin 57) f1162 := by
  apply lratCheckerSound f1162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1162
  · intro a ha; simp [p1162] at ha; subst a; trivial
  · exact checked1162
theorem derived1162 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1162 := by
  apply localUnsat_implies_entails f1162 [c261, c1161, c163, c1159, c63, c50, c191, c34, c1158, c106, c260, c99] c1162 unsat1162 (by rfl) a
  have h0 : Entails.eval a c261 := h 260 (by decide)
  have h1 : Entails.eval a c1161 := derived1161 a h
  have h2 : Entails.eval a c163 := h 162 (by decide)
  have h3 : Entails.eval a c1159 := derived1159 a h
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c1158 := derived1158 a h
  have h9 : Entails.eval a c106 := h 105 (by decide)
  have h10 : Entails.eval a c260 := h 259 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1163 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1163 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1160, some c1156, some c210, some c1162, some c5, some c885, some c50, some c23, some c34, some c163, some c106, some c63, some c191, some c260, some c99, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1163 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1163 : lratChecker f1163 p1163 = .success := by decide +kernel
theorem unsat1163 : Unsatisfiable (PosFin 57) f1163 := by
  apply lratCheckerSound f1163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1163
  · intro a ha; simp [p1163] at ha; subst a; trivial
  · exact checked1163
theorem derived1163 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1163 := by
  apply localUnsat_implies_entails f1163 [c1160, c1156, c210, c1162, c5, c885, c50, c23, c34, c163, c106, c63, c191, c260, c99] c1163 unsat1163 (by rfl) a
  have h0 : Entails.eval a c1160 := derived1160 a h
  have h1 : Entails.eval a c1156 := derived1156 a h
  have h2 : Entails.eval a c210 := h 209 (by decide)
  have h3 : Entails.eval a c1162 := derived1162 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c885 := derived885 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c191 := h 190 (by decide)
  have h13 : Entails.eval a c260 := h 259 (by decide)
  have h14 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1164 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨1, by decide⟩, true), (⟨9, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1164 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c885, some c50, some c263, some c30, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1164 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1164 : lratChecker f1164 p1164 = .success := by decide +kernel
theorem unsat1164 : Unsatisfiable (PosFin 57) f1164 := by
  apply lratCheckerSound f1164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1164
  · intro a ha; simp [p1164] at ha; subst a; trivial
  · exact checked1164
theorem derived1164 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1164 := by
  apply localUnsat_implies_entails f1164 [c5, c885, c50, c263, c30] c1164 unsat1164 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c885 := derived885 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c263 := h 262 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1165 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1165 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1156, some c210, some c1160, some c1163, some c1164, some c261, some c1161, some c30, some c1159, some c50, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1165 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1165 : lratChecker f1165 p1165 = .success := by decide +kernel
theorem unsat1165 : Unsatisfiable (PosFin 57) f1165 := by
  apply lratCheckerSound f1165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1165
  · intro a ha; simp [p1165] at ha; subst a; trivial
  · exact checked1165
theorem derived1165 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1165 := by
  apply localUnsat_implies_entails f1165 [c1156, c210, c1160, c1163, c1164, c261, c1161, c30, c1159, c50] c1165 unsat1165 (by rfl) a
  have h0 : Entails.eval a c1156 := derived1156 a h
  have h1 : Entails.eval a c210 := h 209 (by decide)
  have h2 : Entails.eval a c1160 := derived1160 a h
  have h3 : Entails.eval a c1163 := derived1163 a h
  have h4 : Entails.eval a c1164 := derived1164 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c1161 := derived1161 a h
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c1159 := derived1159 a h
  have h9 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1166 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨27, by decide⟩, false), (⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1166 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1037, some c1147, some c1161, some c1137, some c278, some c107, some c963, some c26, some c110, some c12, some c68, some c157, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1166 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1166 : lratChecker f1166 p1166 = .success := by decide +kernel
theorem unsat1166 : Unsatisfiable (PosFin 57) f1166 := by
  apply lratCheckerSound f1166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1166
  · intro a ha; simp [p1166] at ha; subst a; trivial
  · exact checked1166
theorem derived1166 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1166 := by
  apply localUnsat_implies_entails f1166 [c1037, c1147, c1161, c1137, c278, c107, c963, c26, c110, c12, c68, c157] c1166 unsat1166 (by rfl) a
  have h0 : Entails.eval a c1037 := derived1037 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c1161 := derived1161 a h
  have h3 : Entails.eval a c1137 := derived1137 a h
  have h4 : Entails.eval a c278 := h 277 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c963 := derived963 a h
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1167 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨2, by decide⟩, false), (⟨16, by decide⟩, false), (⟨8, by decide⟩, true), (⟨27, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1167 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c318, some c1147, some c163, some c278, some c61, some c75, some c258, some c167, some c345, some c26, some c195, some c109, some c101, some c193, some c256, some c116, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1167 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1167 : lratChecker f1167 p1167 = .success := by decide +kernel
theorem unsat1167 : Unsatisfiable (PosFin 57) f1167 := by
  apply lratCheckerSound f1167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1167
  · intro a ha; simp [p1167] at ha; subst a; trivial
  · exact checked1167
theorem derived1167 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1167 := by
  apply localUnsat_implies_entails f1167 [c318, c1147, c163, c278, c61, c75, c258, c167, c345, c26, c195, c109, c101, c193, c256, c116] c1167 unsat1167 (by rfl) a
  have h0 : Entails.eval a c318 := h 317 (by decide)
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c163 := h 162 (by decide)
  have h3 : Entails.eval a c278 := h 277 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  have h7 : Entails.eval a c167 := h 166 (by decide)
  have h8 : Entails.eval a c345 := h 344 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c195 := h 194 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c193 := h 192 (by decide)
  have h14 : Entails.eval a c256 := h 255 (by decide)
  have h15 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1168 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1168 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1165, some c261, some c1037, some c1147, some c1166, some c113, some c1, some c107, some c19, some c202, some c12, some c1167, some c218, some c222, some c347, some c269, some c75, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1168 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1168 : lratChecker f1168 p1168 = .success := by decide +kernel
theorem unsat1168 : Unsatisfiable (PosFin 57) f1168 := by
  apply lratCheckerSound f1168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1168
  · intro a ha; simp [p1168] at ha; subst a; trivial
  · exact checked1168
theorem derived1168 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1168 := by
  apply localUnsat_implies_entails f1168 [c1165, c261, c1037, c1147, c1166, c113, c1, c107, c19, c202, c12, c1167, c218, c222, c347, c269, c75] c1168 unsat1168 (by rfl) a
  have h0 : Entails.eval a c1165 := derived1165 a h
  have h1 : Entails.eval a c261 := h 260 (by decide)
  have h2 : Entails.eval a c1037 := derived1037 a h
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c1166 := derived1166 a h
  have h5 : Entails.eval a c113 := h 112 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c19 := h 18 (by decide)
  have h9 : Entails.eval a c202 := h 201 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c1167 := derived1167 a h
  have h12 : Entails.eval a c218 := h 217 (by decide)
  have h13 : Entails.eval a c222 := h 221 (by decide)
  have h14 : Entails.eval a c347 := h 346 (by decide)
  have h15 : Entails.eval a c269 := h 268 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1169 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨25, by decide⟩, false), (⟨30, by decide⟩, false), (⟨17, by decide⟩, true), (⟨7, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1169 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1037, some c1147, some c107, some c42, some c19, some c26, some c34, some c202, some c270, some c167, some c12, some c218, some c75, some c108, some c352, some c73, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1169 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1169 : lratChecker f1169 p1169 = .success := by decide +kernel
theorem unsat1169 : Unsatisfiable (PosFin 57) f1169 := by
  apply lratCheckerSound f1169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1169
  · intro a ha; simp [p1169] at ha; subst a; trivial
  · exact checked1169
theorem derived1169 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1169 := by
  apply localUnsat_implies_entails f1169 [c1037, c1147, c107, c42, c19, c26, c34, c202, c270, c167, c12, c218, c75, c108, c352, c73] c1169 unsat1169 (by rfl) a
  have h0 : Entails.eval a c1037 := derived1037 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c270 := h 269 (by decide)
  have h9 : Entails.eval a c167 := h 166 (by decide)
  have h10 : Entails.eval a c12 := h 11 (by decide)
  have h11 : Entails.eval a c218 := h 217 (by decide)
  have h12 : Entails.eval a c75 := h 74 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c352 := h 351 (by decide)
  have h15 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1170 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1170 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1165, some c1147, some c261, some c1037, some c1168, some c210, some c206, some c1169, some c1, some c21, some c963, some c1161, some c1137, some c269, some c26, some c110, some c12, some c68, some c157, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1170 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1170 : lratChecker f1170 p1170 = .success := by decide +kernel
theorem unsat1170 : Unsatisfiable (PosFin 57) f1170 := by
  apply lratCheckerSound f1170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1170
  · intro a ha; simp [p1170] at ha; subst a; trivial
  · exact checked1170
theorem derived1170 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1170 := by
  apply localUnsat_implies_entails f1170 [c1165, c1147, c261, c1037, c1168, c210, c206, c1169, c1, c21, c963, c1161, c1137, c269, c26, c110, c12, c68, c157] c1170 unsat1170 (by rfl) a
  have h0 : Entails.eval a c1165 := derived1165 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1168 := derived1168 a h
  have h5 : Entails.eval a c210 := h 209 (by decide)
  have h6 : Entails.eval a c206 := h 205 (by decide)
  have h7 : Entails.eval a c1169 := derived1169 a h
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c963 := derived963 a h
  have h11 : Entails.eval a c1161 := derived1161 a h
  have h12 : Entails.eval a c1137 := derived1137 a h
  have h13 : Entails.eval a c269 := h 268 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c68 := h 67 (by decide)
  have h18 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1171 : DefaultClause 57 := directClause [(⟨29, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1171 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1165, some c1170, some c5, some c105, some c949, some c1037, some c112, some c263, some c34, some c885, some c131, some c110, some c202, some c9, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1171 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1171 : lratChecker f1171 p1171 = .success := by decide +kernel
theorem unsat1171 : Unsatisfiable (PosFin 57) f1171 := by
  apply lratCheckerSound f1171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1171
  · intro a ha; simp [p1171] at ha; subst a; trivial
  · exact checked1171
theorem derived1171 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1171 := by
  apply localUnsat_implies_entails f1171 [c1147, c1165, c1170, c5, c105, c949, c1037, c112, c263, c34, c885, c131, c110, c202, c9] c1171 unsat1171 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1165 := derived1165 a h
  have h2 : Entails.eval a c1170 := derived1170 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c949 := derived949 a h
  have h6 : Entails.eval a c1037 := derived1037 a h
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c885 := derived885 a h
  have h11 : Entails.eval a c131 := h 130 (by decide)
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c202 := h 201 (by decide)
  have h14 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1172 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1172 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1037, some c1147, some c1, some c30, some c21, some c963, some c198, some c1161, some c111, some c155, some c26, some c72, some c349, some c161, some c69, some c17, some c110, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1172 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1172 : lratChecker f1172 p1172 = .success := by decide +kernel
theorem unsat1172 : Unsatisfiable (PosFin 57) f1172 := by
  apply lratCheckerSound f1172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1172
  · intro a ha; simp [p1172] at ha; subst a; trivial
  · exact checked1172
theorem derived1172 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1172 := by
  apply localUnsat_implies_entails f1172 [c1037, c1147, c1, c30, c21, c963, c198, c1161, c111, c155, c26, c72, c349, c161, c69, c17, c110] c1172 unsat1172 (by rfl) a
  have h0 : Entails.eval a c1037 := derived1037 a h
  have h1 : Entails.eval a c1147 := derived1147 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c963 := derived963 a h
  have h6 : Entails.eval a c198 := h 197 (by decide)
  have h7 : Entails.eval a c1161 := derived1161 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c155 := h 154 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c349 := h 348 (by decide)
  have h13 : Entails.eval a c161 := h 160 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1173 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨43, by decide⟩, true), (⟨41, by decide⟩, true), (⟨7, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1173 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1161, some c163, some c63, some c191, some c183, some c355, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1173 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1173 : lratChecker f1173 p1173 = .success := by decide +kernel
theorem unsat1173 : Unsatisfiable (PosFin 57) f1173 := by
  apply lratCheckerSound f1173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1173
  · intro a ha; simp [p1173] at ha; subst a; trivial
  · exact checked1173
theorem derived1173 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1173 := by
  apply localUnsat_implies_entails f1173 [c1161, c163, c63, c191, c183, c355] c1173 unsat1173 (by rfl) a
  have h0 : Entails.eval a c1161 := derived1161 a h
  have h1 : Entails.eval a c163 := h 162 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c183 := h 182 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1174 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨42, by decide⟩, false), (⟨26, by decide⟩, false), (⟨32, by decide⟩, true), (⟨43, by decide⟩, true), (⟨3, by decide⟩, false), (⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1174 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c84, some c291, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p1174 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1174 : lratChecker f1174 p1174 = .success := by decide +kernel
theorem unsat1174 : Unsatisfiable (PosFin 57) f1174 := by
  apply lratCheckerSound f1174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1174
  · intro a ha; simp [p1174] at ha; subst a; trivial
  · exact checked1174
theorem derived1174 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1174 := by
  apply localUnsat_implies_entails f1174 [c45, c84, c291] c1174 unsat1174 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c84 := h 83 (by decide)
  have h2 : Entails.eval a c291 := h 290 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1175 : DefaultClause 57 := directClause [(⟨27, by decide⟩, true), (⟨42, by decide⟩, false), (⟨18, by decide⟩, false), (⟨32, by decide⟩, true), (⟨43, by decide⟩, true), (⟨19, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1175 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c211, some c291, some c236, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨42, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false))]
def p1175 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1175 : lratChecker f1175 p1175 = .success := by decide +kernel
theorem unsat1175 : Unsatisfiable (PosFin 57) f1175 := by
  apply lratCheckerSound f1175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1175
  · intro a ha; simp [p1175] at ha; subst a; trivial
  · exact checked1175
theorem derived1175 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1175 := by
  apply localUnsat_implies_entails f1175 [c211, c291, c236] c1175 unsat1175 (by rfl) a
  have h0 : Entails.eval a c211 := h 210 (by decide)
  have h1 : Entails.eval a c291 := h 290 (by decide)
  have h2 : Entails.eval a c236 := h 235 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1176 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨2, by decide⟩, true), (⟨26, by decide⟩, false), (⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1176 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c273, some c69, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1176 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1176 : lratChecker f1176 p1176 = .success := by decide +kernel
theorem unsat1176 : Unsatisfiable (PosFin 57) f1176 := by
  apply lratCheckerSound f1176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1176
  · intro a ha; simp [p1176] at ha; subst a; trivial
  · exact checked1176
theorem derived1176 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1176 := by
  apply localUnsat_implies_entails f1176 [c163, c273, c69] c1176 unsat1176 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1177 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1177 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c1172, some c77, some c1037, some c117, some c1147, some c106, some c26, some c34, some c111, some c86, some c1173, some c113, some c44, some c151, some c202, some c167, some c121, some c144, some c169, some c761, some c1174, some c1175, some c1176, some c223, some c236, some c293, some c710, some c240, some c165, some c24, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1177 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1177 : lratChecker f1177 p1177 = .success := by decide +kernel
theorem unsat1177 : Unsatisfiable (PosFin 57) f1177 := by
  apply lratCheckerSound f1177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1177
  · intro a ha; simp [p1177] at ha; subst a; trivial
  · exact checked1177
theorem derived1177 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1177 := by
  apply localUnsat_implies_entails f1177 [c137, c1172, c77, c1037, c117, c1147, c106, c26, c34, c111, c86, c1173, c113, c44, c151, c202, c167, c121, c144, c169, c761, c1174, c1175, c1176, c223, c236, c293, c710, c240, c165, c24] c1177 unsat1177 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c1172 := derived1172 a h
  have h2 : Entails.eval a c77 := h 76 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c1147 := derived1147 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c26 := h 25 (by decide)
  have h8 : Entails.eval a c34 := h 33 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c86 := h 85 (by decide)
  have h11 : Entails.eval a c1173 := derived1173 a h
  have h12 : Entails.eval a c113 := h 112 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  have h14 : Entails.eval a c151 := h 150 (by decide)
  have h15 : Entails.eval a c202 := h 201 (by decide)
  have h16 : Entails.eval a c167 := h 166 (by decide)
  have h17 : Entails.eval a c121 := h 120 (by decide)
  have h18 : Entails.eval a c144 := h 143 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c761 := derived761 a h
  have h21 : Entails.eval a c1174 := derived1174 a h
  have h22 : Entails.eval a c1175 := derived1175 a h
  have h23 : Entails.eval a c1176 := derived1176 a h
  have h24 : Entails.eval a c223 := h 222 (by decide)
  have h25 : Entails.eval a c236 := h 235 (by decide)
  have h26 : Entails.eval a c293 := h 292 (by decide)
  have h27 : Entails.eval a c710 := derived710 a h
  have h28 : Entails.eval a c240 := h 239 (by decide)
  have h29 : Entails.eval a c165 := h 164 (by decide)
  have h30 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1178 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨3, by decide⟩, false), (⟨8, by decide⟩, true), (⟨7, by decide⟩, true), (⟨17, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1178 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c45, some c1176, some c218, some c222, some c347, some c64, some c28, some c260, some c252, some c97, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1178 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1178 : lratChecker f1178 p1178 = .success := by decide +kernel
theorem unsat1178 : Unsatisfiable (PosFin 57) f1178 := by
  apply lratCheckerSound f1178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1178
  · intro a ha; simp [p1178] at ha; subst a; trivial
  · exact checked1178
theorem derived1178 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1178 := by
  apply localUnsat_implies_entails f1178 [c45, c1176, c218, c222, c347, c64, c28, c260, c252, c97] c1178 unsat1178 (by rfl) a
  have h0 : Entails.eval a c45 := h 44 (by decide)
  have h1 : Entails.eval a c1176 := derived1176 a h
  have h2 : Entails.eval a c218 := h 217 (by decide)
  have h3 : Entails.eval a c222 := h 221 (by decide)
  have h4 : Entails.eval a c347 := h 346 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c260 := h 259 (by decide)
  have h8 : Entails.eval a c252 := h 251 (by decide)
  have h9 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1179 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1179 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1171, some c117, some c261, some c1037, some c137, some c1172, some c77, some c86, some c1173, some c113, some c1177, some c121, some c144, some c169, some c1178, some c210, some c1175, some c313, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1179 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1179 : lratChecker f1179 p1179 = .success := by decide +kernel
theorem unsat1179 : Unsatisfiable (PosFin 57) f1179 := by
  apply lratCheckerSound f1179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1179
  · intro a ha; simp [p1179] at ha; subst a; trivial
  · exact checked1179
theorem derived1179 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1179 := by
  apply localUnsat_implies_entails f1179 [c1171, c117, c261, c1037, c137, c1172, c77, c86, c1173, c113, c1177, c121, c144, c169, c1178, c210, c1175, c313] c1179 unsat1179 (by rfl) a
  have h0 : Entails.eval a c1171 := derived1171 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c1172 := derived1172 a h
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c1173 := derived1173 a h
  have h9 : Entails.eval a c113 := h 112 (by decide)
  have h10 : Entails.eval a c1177 := derived1177 a h
  have h11 : Entails.eval a c121 := h 120 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c169 := h 168 (by decide)
  have h14 : Entails.eval a c1178 := derived1178 a h
  have h15 : Entails.eval a c210 := h 209 (by decide)
  have h16 : Entails.eval a c1175 := derived1175 a h
  have h17 : Entails.eval a c313 := h 312 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1180 : DefaultClause 57 := directClause [(⟨3, by decide⟩, false), (⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1180 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1171, some c117, some c261, some c1177, some c1147, some c111, some c1179, some c200, some c202, some c17, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1180 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1180 : lratChecker f1180 p1180 = .success := by decide +kernel
theorem unsat1180 : Unsatisfiable (PosFin 57) f1180 := by
  apply lratCheckerSound f1180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1180
  · intro a ha; simp [p1180] at ha; subst a; trivial
  · exact checked1180
theorem derived1180 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1180 := by
  apply localUnsat_implies_entails f1180 [c1171, c117, c261, c1177, c1147, c111, c1179, c200, c202, c17] c1180 unsat1180 (by rfl) a
  have h0 : Entails.eval a c1171 := derived1171 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c1177 := derived1177 a h
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c1179 := derived1179 a h
  have h7 : Entails.eval a c200 := h 199 (by decide)
  have h8 : Entails.eval a c202 := h 201 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1181 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1181 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1171, some c117, some c261, some c1037, some c1172, some c1177, some c1180, some c23, some c1158, some c163, some c63, some c191, some c260, some c99, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1181 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1181 : lratChecker f1181 p1181 = .success := by decide +kernel
theorem unsat1181 : Unsatisfiable (PosFin 57) f1181 := by
  apply lratCheckerSound f1181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1181
  · intro a ha; simp [p1181] at ha; subst a; trivial
  · exact checked1181
theorem derived1181 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1181 := by
  apply localUnsat_implies_entails f1181 [c1171, c117, c261, c1037, c1172, c1177, c1180, c23, c1158, c163, c63, c191, c260, c99] c1181 unsat1181 (by rfl) a
  have h0 : Entails.eval a c1171 := derived1171 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c1037 := derived1037 a h
  have h4 : Entails.eval a c1172 := derived1172 a h
  have h5 : Entails.eval a c1177 := derived1177 a h
  have h6 : Entails.eval a c1180 := derived1180 a h
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c1158 := derived1158 a h
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c260 := h 259 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1182 : DefaultClause 57 := directClause [(⟨55, by decide⟩, false), (⟨8, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1182 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c191, some c260, some c99, some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1182 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1182 : lratChecker f1182 p1182 = .success := by decide +kernel
theorem unsat1182 : Unsatisfiable (PosFin 57) f1182 := by
  apply lratCheckerSound f1182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1182
  · intro a ha; simp [p1182] at ha; subst a; trivial
  · exact checked1182
theorem derived1182 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1182 := by
  apply localUnsat_implies_entails f1182 [c191, c260, c99] c1182 unsat1182 (by rfl) a
  have h0 : Entails.eval a c191 := h 190 (by decide)
  have h1 : Entails.eval a c260 := h 259 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1183 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1183 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1181, some c1171, some c117, some c261, some c1147, some c23, some c34, some c30, some c1158, some c163, some c106, some c1137, some c19, some c113, some c202, some c42, some c121, some c144, some c210, some c273, some c1182, some c338, some c252, some c301, some c99, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1183 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1183 : lratChecker f1183 p1183 = .success := by decide +kernel
theorem unsat1183 : Unsatisfiable (PosFin 57) f1183 := by
  apply lratCheckerSound f1183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1183
  · intro a ha; simp [p1183] at ha; subst a; trivial
  · exact checked1183
theorem derived1183 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1183 := by
  apply localUnsat_implies_entails f1183 [c1181, c1171, c117, c261, c1147, c23, c34, c30, c1158, c163, c106, c1137, c19, c113, c202, c42, c121, c144, c210, c273, c1182, c338, c252, c301, c99] c1183 unsat1183 (by rfl) a
  have h0 : Entails.eval a c1181 := derived1181 a h
  have h1 : Entails.eval a c1171 := derived1171 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c261 := h 260 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c30 := h 29 (by decide)
  have h8 : Entails.eval a c1158 := derived1158 a h
  have h9 : Entails.eval a c163 := h 162 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c1137 := derived1137 a h
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c202 := h 201 (by decide)
  have h15 : Entails.eval a c42 := h 41 (by decide)
  have h16 : Entails.eval a c121 := h 120 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  have h18 : Entails.eval a c210 := h 209 (by decide)
  have h19 : Entails.eval a c273 := h 272 (by decide)
  have h20 : Entails.eval a c1182 := derived1182 a h
  have h21 : Entails.eval a c338 := h 337 (by decide)
  have h22 : Entails.eval a c252 := h 251 (by decide)
  have h23 : Entails.eval a c301 := h 300 (by decide)
  have h24 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1184 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, true), (⟨19, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1184 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1137, some c19, some c113, some c1, some c202, some c144, some c12, some c108, some c45, some c210, some c42, some c26, some c167, some c270, some c75, some c73, some c218, some c352, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1184 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1184 : lratChecker f1184 p1184 = .success := by decide +kernel
theorem unsat1184 : Unsatisfiable (PosFin 57) f1184 := by
  apply lratCheckerSound f1184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1184
  · intro a ha; simp [p1184] at ha; subst a; trivial
  · exact checked1184
theorem derived1184 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1184 := by
  apply localUnsat_implies_entails f1184 [c1147, c1137, c19, c113, c1, c202, c144, c12, c108, c45, c210, c42, c26, c167, c270, c75, c73, c218, c352] c1184 unsat1184 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1137 := derived1137 a h
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c202 := h 201 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  have h9 : Entails.eval a c45 := h 44 (by decide)
  have h10 : Entails.eval a c210 := h 209 (by decide)
  have h11 : Entails.eval a c42 := h 41 (by decide)
  have h12 : Entails.eval a c26 := h 25 (by decide)
  have h13 : Entails.eval a c167 := h 166 (by decide)
  have h14 : Entails.eval a c270 := h 269 (by decide)
  have h15 : Entails.eval a c75 := h 74 (by decide)
  have h16 : Entails.eval a c73 := h 72 (by decide)
  have h17 : Entails.eval a c218 := h 217 (by decide)
  have h18 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1185 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨6, by decide⟩, true), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨5, by decide⟩, true), (⟨21, by decide⟩, false), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1185 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c163, some c63, some c258, some c102, some c61, some c352, some c72, some c108, some c541, some c12, some c187, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1185 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1185 : lratChecker f1185 p1185 = .success := by decide +kernel
theorem unsat1185 : Unsatisfiable (PosFin 57) f1185 := by
  apply lratCheckerSound f1185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1185
  · intro a ha; simp [p1185] at ha; subst a; trivial
  · exact checked1185
theorem derived1185 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1185 := by
  apply localUnsat_implies_entails f1185 [c163, c63, c258, c102, c61, c352, c72, c108, c541, c12, c187] c1185 unsat1185 (by rfl) a
  have h0 : Entails.eval a c163 := h 162 (by decide)
  have h1 : Entails.eval a c63 := h 62 (by decide)
  have h2 : Entails.eval a c258 := h 257 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c352 := h 351 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  have h8 : Entails.eval a c541 := derived541 a h
  have h9 : Entails.eval a c12 := h 11 (by decide)
  have h10 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1186 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1186 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1171, some c117, some c261, some c1181, some c1183, some c1184, some c1147, some c107, some c106, some c26, some c1185, some c218, some c1161, some c113, some c44, some c270, some c151, some c210, some c202, some c144, some c12, some c45, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1186 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1186 : lratChecker f1186 p1186 = .success := by decide +kernel
theorem unsat1186 : Unsatisfiable (PosFin 57) f1186 := by
  apply lratCheckerSound f1186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1186
  · intro a ha; simp [p1186] at ha; subst a; trivial
  · exact checked1186
theorem derived1186 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1186 := by
  apply localUnsat_implies_entails f1186 [c1171, c117, c261, c1181, c1183, c1184, c1147, c107, c106, c26, c1185, c218, c1161, c113, c44, c270, c151, c210, c202, c144, c12, c45] c1186 unsat1186 (by rfl) a
  have h0 : Entails.eval a c1171 := derived1171 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c261 := h 260 (by decide)
  have h3 : Entails.eval a c1181 := derived1181 a h
  have h4 : Entails.eval a c1183 := derived1183 a h
  have h5 : Entails.eval a c1184 := derived1184 a h
  have h6 : Entails.eval a c1147 := derived1147 a h
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c106 := h 105 (by decide)
  have h9 : Entails.eval a c26 := h 25 (by decide)
  have h10 : Entails.eval a c1185 := derived1185 a h
  have h11 : Entails.eval a c218 := h 217 (by decide)
  have h12 : Entails.eval a c1161 := derived1161 a h
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c44 := h 43 (by decide)
  have h15 : Entails.eval a c270 := h 269 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  have h17 : Entails.eval a c210 := h 209 (by decide)
  have h18 : Entails.eval a c202 := h 201 (by decide)
  have h19 : Entails.eval a c144 := h 143 (by decide)
  have h20 : Entails.eval a c12 := h 11 (by decide)
  have h21 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1187 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1187 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1171, some c117, some c137, some c261, some c1181, some c1183, some c1184, some c1186, some c1, some c21, some c963, some c1161, some c155, some c26, some c110, some c12, some c157, some c58, some c68, some c185, some c187, some c328, some c320, some c345, some c355, some c183, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1187 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1187 : lratChecker f1187 p1187 = .success := by decide +kernel
theorem unsat1187 : Unsatisfiable (PosFin 57) f1187 := by
  apply lratCheckerSound f1187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1187
  · intro a ha; simp [p1187] at ha; subst a; trivial
  · exact checked1187
theorem derived1187 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1187 := by
  apply localUnsat_implies_entails f1187 [c1147, c1171, c117, c137, c261, c1181, c1183, c1184, c1186, c1, c21, c963, c1161, c155, c26, c110, c12, c157, c58, c68, c185, c187, c328, c320, c345, c355, c183] c1187 unsat1187 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1171 := derived1171 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c137 := h 136 (by decide)
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c1181 := derived1181 a h
  have h6 : Entails.eval a c1183 := derived1183 a h
  have h7 : Entails.eval a c1184 := derived1184 a h
  have h8 : Entails.eval a c1186 := derived1186 a h
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c963 := derived963 a h
  have h12 : Entails.eval a c1161 := derived1161 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c12 := h 11 (by decide)
  have h17 : Entails.eval a c157 := h 156 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c68 := h 67 (by decide)
  have h20 : Entails.eval a c185 := h 184 (by decide)
  have h21 : Entails.eval a c187 := h 186 (by decide)
  have h22 : Entails.eval a c328 := h 327 (by decide)
  have h23 : Entails.eval a c320 := h 319 (by decide)
  have h24 : Entails.eval a c345 := h 344 (by decide)
  have h25 : Entails.eval a c355 := h 354 (by decide)
  have h26 : Entails.eval a c183 := h 182 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1188 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨32, by decide⟩, false), (⟨47, by decide⟩, true), (⟨45, by decide⟩, false), (⟨39, by decide⟩, true), (⟨35, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨33, by decide⟩, false), (⟨16, by decide⟩, true), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1188 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c110, some c328, some c320, some c175, some c91, some c236, some c296, some c56, some c314, some c69, some c285, some c273, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p1188 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1188 : lratChecker f1188 p1188 = .success := by decide +kernel
theorem unsat1188 : Unsatisfiable (PosFin 57) f1188 := by
  apply lratCheckerSound f1188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1188
  · intro a ha; simp [p1188] at ha; subst a; trivial
  · exact checked1188
theorem derived1188 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1188 := by
  apply localUnsat_implies_entails f1188 [c55, c110, c328, c320, c175, c91, c236, c296, c56, c314, c69, c285, c273] c1188 unsat1188 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c328 := h 327 (by decide)
  have h3 : Entails.eval a c320 := h 319 (by decide)
  have h4 : Entails.eval a c175 := h 174 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c236 := h 235 (by decide)
  have h7 : Entails.eval a c296 := h 295 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c314 := h 313 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  have h11 : Entails.eval a c285 := h 284 (by decide)
  have h12 : Entails.eval a c273 := h 272 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1189 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨9, by decide⟩, false), (⟨10, by decide⟩, false), (⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1189 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c182, some c187, some c472, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1189 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1189 : lratChecker f1189 p1189 = .success := by decide +kernel
theorem unsat1189 : Unsatisfiable (PosFin 57) f1189 := by
  apply lratCheckerSound f1189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1189
  · intro a ha; simp [p1189] at ha; subst a; trivial
  · exact checked1189
theorem derived1189 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1189 := by
  apply localUnsat_implies_entails f1189 [c182, c187, c472] c1189 unsat1189 (by rfl) a
  have h0 : Entails.eval a c182 := h 181 (by decide)
  have h1 : Entails.eval a c187 := h 186 (by decide)
  have h2 : Entails.eval a c472 := derived472 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1190 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1190 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c1187, some c115, some c1147, some c5, some c12, some c261, some c202, some c122, some c21, some c963, some c29, some c127, some c1161, some c155, some c1189, some c345, some c258, some c61, some c278, some c137, some c578, some c151, some c1188, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1190 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1190 : lratChecker f1190 p1190 = .success := by decide +kernel
theorem unsat1190 : Unsatisfiable (PosFin 57) f1190 := by
  apply lratCheckerSound f1190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1190
  · intro a ha; simp [p1190] at ha; subst a; trivial
  · exact checked1190
theorem derived1190 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1190 := by
  apply localUnsat_implies_entails f1190 [c110, c1187, c115, c1147, c5, c12, c261, c202, c122, c21, c963, c29, c127, c1161, c155, c1189, c345, c258, c61, c278, c137, c578, c151, c1188] c1190 unsat1190 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c1187 := derived1187 a h
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1147 := derived1147 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c261 := h 260 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  have h10 : Entails.eval a c963 := derived963 a h
  have h11 : Entails.eval a c29 := h 28 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c1161 := derived1161 a h
  have h14 : Entails.eval a c155 := h 154 (by decide)
  have h15 : Entails.eval a c1189 := derived1189 a h
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c258 := h 257 (by decide)
  have h18 : Entails.eval a c61 := h 60 (by decide)
  have h19 : Entails.eval a c278 := h 277 (by decide)
  have h20 : Entails.eval a c137 := h 136 (by decide)
  have h21 : Entails.eval a c578 := derived578 a h
  have h22 : Entails.eval a c151 := h 150 (by decide)
  have h23 : Entails.eval a c1188 := derived1188 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1191 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1191 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1187, some c115, some c3, some c110, some c1190, some c112, some c111, some c50, some c117, some c261, some c122, some c21, some c1161, some c155, some c69, some c72, some c349, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1191 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1191 : lratChecker f1191 p1191 = .success := by decide +kernel
theorem unsat1191 : Unsatisfiable (PosFin 57) f1191 := by
  apply lratCheckerSound f1191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1191
  · intro a ha; simp [p1191] at ha; subst a; trivial
  · exact checked1191
theorem derived1191 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1191 := by
  apply localUnsat_implies_entails f1191 [c1187, c115, c3, c110, c1190, c112, c111, c50, c117, c261, c122, c21, c1161, c155, c69, c72, c349] c1191 unsat1191 (by rfl) a
  have h0 : Entails.eval a c1187 := derived1187 a h
  have h1 : Entails.eval a c115 := h 114 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c1190 := derived1190 a h
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c117 := h 116 (by decide)
  have h9 : Entails.eval a c261 := h 260 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c1161 := derived1161 a h
  have h13 : Entails.eval a c155 := h 154 (by decide)
  have h14 : Entails.eval a c69 := h 68 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c349 := h 348 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1192 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨13, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1192 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c5, some c117, some c50, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false))]
def p1192 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1192 : lratChecker f1192 p1192 = .success := by decide +kernel
theorem unsat1192 : Unsatisfiable (PosFin 57) f1192 := by
  apply lratCheckerSound f1192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1192
  · intro a ha; simp [p1192] at ha; subst a; trivial
  · exact checked1192
theorem derived1192 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1192 := by
  apply localUnsat_implies_entails f1192 [c5, c117, c50] c1192 unsat1192 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1193 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨2, by decide⟩, true), (⟨38, by decide⟩, false), (⟨4, by decide⟩, true), (⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1193 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c69, some c72, some c350, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p1193 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1193 : lratChecker f1193 p1193 = .success := by decide +kernel
theorem unsat1193 : Unsatisfiable (PosFin 57) f1193 := by
  apply lratCheckerSound f1193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1193
  · intro a ha; simp [p1193] at ha; subst a; trivial
  · exact checked1193
theorem derived1193 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1193 := by
  apply localUnsat_implies_entails f1193 [c69, c72, c350] c1193 unsat1193 (by rfl) a
  have h0 : Entails.eval a c69 := h 68 (by decide)
  have h1 : Entails.eval a c72 := h 71 (by decide)
  have h2 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1194 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨38, by decide⟩, false), (⟨29, by decide⟩, true), (⟨35, by decide⟩, false), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c159, some c273, some c144, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 57) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c159, c273, c144] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c159 := h 158 (by decide)
  have h1 : Entails.eval a c273 := h 272 (by decide)
  have h2 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1195 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨25, by decide⟩, true), (⟨41, by decide⟩, true), (⟨45, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c287, some c207, some c240, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p1195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 57) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c287, c207, c240] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c287 := h 286 (by decide)
  have h1 : Entails.eval a c207 := h 206 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 57 := directClause [(⟨38, by decide⟩, false), (⟨48, by decide⟩, false), (⟨32, by decide⟩, false), (⟨29, by decide⟩, true), (⟨5, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c137, some c963, some c154, some c77, some c44, some c1194, some c217, some c236, some c1195, some c285, some c315, some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 57) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c137, c963, c154, c77, c44, c1194, c217, c236, c1195, c285, c315] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c137 := h 136 (by decide)
  have h1 : Entails.eval a c963 := derived963 a h
  have h2 : Entails.eval a c154 := h 153 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c1194 := derived1194 a h
  have h6 : Entails.eval a c217 := h 216 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c1195 := derived1195 a h
  have h9 : Entails.eval a c285 := h 284 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 57 := directClause [(⟨6, by decide⟩, false), (⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c1191, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 57) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c106, c1191] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c1191 := derived1191 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1198 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨38, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1192, some c50, some c137, some c1004, some c86, some c1196, some c175, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 57) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c1192, c50, c137, c1004, c86, c1196, c175] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c1192 := derived1192 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c137 := h 136 (by decide)
  have h3 : Entails.eval a c1004 := derived1004 a h
  have h4 : Entails.eval a c86 := h 85 (by decide)
  have h5 : Entails.eval a c1196 := derived1196 a h
  have h6 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1199 : DefaultClause 57 := directClause [(⟨48, by decide⟩, false), (⟨18, by decide⟩, false), (⟨25, by decide⟩, true), (⟨45, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c80, some c236, some c1195, some c285, some c315, some (DefaultClause.unit (⟨48, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨45, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p1199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 57) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c80, c236, c1195, c285, c315] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c80 := h 79 (by decide)
  have h1 : Entails.eval a c236 := h 235 (by decide)
  have h2 : Entails.eval a c1195 := derived1195 a h
  have h3 : Entails.eval a c285 := h 284 (by decide)
  have h4 : Entails.eval a c315 := h 314 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 57 := directClause [(⟨29, by decide⟩, true), (⟨38, by decide⟩, false), (⟨8, by decide⟩, false), (⟨24, by decide⟩, false), (⟨35, by decide⟩, false), (⟨16, by decide⟩, true), (⟨9, by decide⟩, false), (⟨17, by decide⟩, true), (⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨11, by decide⟩, true), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1198, some c154, some c963, some c1192, some c137, some c1004, some c1194, some c44, some c217, some c1199, some c175, some c328, some c372, some c68, some c177, some c45, some c201, some c144, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 57) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c1198, c154, c963, c1192, c137, c1004, c1194, c44, c217, c1199, c175, c328, c372, c68, c177, c45, c201, c144] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c1198 := derived1198 a h
  have h1 : Entails.eval a c154 := h 153 (by decide)
  have h2 : Entails.eval a c963 := derived963 a h
  have h3 : Entails.eval a c1192 := derived1192 a h
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c1004 := derived1004 a h
  have h6 : Entails.eval a c1194 := derived1194 a h
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c217 := h 216 (by decide)
  have h9 : Entails.eval a c1199 := derived1199 a h
  have h10 : Entails.eval a c175 := h 174 (by decide)
  have h11 : Entails.eval a c328 := h 327 (by decide)
  have h12 : Entails.eval a c372 := h 371 (by decide)
  have h13 : Entails.eval a c68 := h 67 (by decide)
  have h14 : Entails.eval a c177 := h 176 (by decide)
  have h15 : Entails.eval a c45 := h 44 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1201 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, true), (⟨33, by decide⟩, true), (⟨38, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c116, some c219, some c165, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 57) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c116, c219, c165] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 57 := directClause [(⟨8, by decide⟩, false), (⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1187, some c3, some c115, some c1192, some c261, some c684, some c127, some c122, some c1161, some c1147, some c1197, some c26, some c963, some c154, some c107, some c1198, some c1200, some c318, some c278, some c61, some c258, some c104, some c182, some c1201, some c256, some c336, some c100, some c350, some c108, some c68, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 57) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c1187, c3, c115, c1192, c261, c684, c127, c122, c1161, c1147, c1197, c26, c963, c154, c107, c1198, c1200, c318, c278, c61, c258, c104, c182, c1201, c256, c336, c100, c350, c108, c68] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c1187 := derived1187 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c115 := h 114 (by decide)
  have h3 : Entails.eval a c1192 := derived1192 a h
  have h4 : Entails.eval a c261 := h 260 (by decide)
  have h5 : Entails.eval a c684 := derived684 a h
  have h6 : Entails.eval a c127 := h 126 (by decide)
  have h7 : Entails.eval a c122 := h 121 (by decide)
  have h8 : Entails.eval a c1161 := derived1161 a h
  have h9 : Entails.eval a c1147 := derived1147 a h
  have h10 : Entails.eval a c1197 := derived1197 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c963 := derived963 a h
  have h13 : Entails.eval a c154 := h 153 (by decide)
  have h14 : Entails.eval a c107 := h 106 (by decide)
  have h15 : Entails.eval a c1198 := derived1198 a h
  have h16 : Entails.eval a c1200 := derived1200 a h
  have h17 : Entails.eval a c318 := h 317 (by decide)
  have h18 : Entails.eval a c278 := h 277 (by decide)
  have h19 : Entails.eval a c61 := h 60 (by decide)
  have h20 : Entails.eval a c258 := h 257 (by decide)
  have h21 : Entails.eval a c104 := h 103 (by decide)
  have h22 : Entails.eval a c182 := h 181 (by decide)
  have h23 : Entails.eval a c1201 := derived1201 a h
  have h24 : Entails.eval a c256 := h 255 (by decide)
  have h25 : Entails.eval a c336 := h 335 (by decide)
  have h26 : Entails.eval a c100 := h 99 (by decide)
  have h27 : Entails.eval a c350 := h 349 (by decide)
  have h28 : Entails.eval a c108 := h 107 (by decide)
  have h29 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1203 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1147, some c1187, some c3, some c115, some c1192, some c261, some c122, some c684, some c1161, some c127, some c1202, some c1137, some c949, some c111, some c50, some c17, some c137, some c578, some c1004, some c201, some c86, some c144, some c175, some c786, some c315, some c273, some c317, some c69, some c58, some c2, some c155, some c279, some c353, some c1119, some c303, some c301, some c236, some c21, some c292, some c296, some c207, some c219, some c1201, some c101, some c64, some c77, some c26, some c193, some c355, some c343, some c183, some c393, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 57) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c1147, c1187, c3, c115, c1192, c261, c122, c684, c1161, c127, c1202, c1137, c949, c111, c50, c17, c137, c578, c1004, c201, c86, c144, c175, c786, c315, c273, c317, c69, c58, c2, c155, c279, c353, c1119, c303, c301, c236, c21, c292, c296, c207, c219, c1201, c101, c64, c77, c26, c193, c355, c343, c183, c393] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c1147 := derived1147 a h
  have h1 : Entails.eval a c1187 := derived1187 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c1192 := derived1192 a h
  have h5 : Entails.eval a c261 := h 260 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  have h7 : Entails.eval a c684 := derived684 a h
  have h8 : Entails.eval a c1161 := derived1161 a h
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c1202 := derived1202 a h
  have h11 : Entails.eval a c1137 := derived1137 a h
  have h12 : Entails.eval a c949 := derived949 a h
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c50 := h 49 (by decide)
  have h15 : Entails.eval a c17 := h 16 (by decide)
  have h16 : Entails.eval a c137 := h 136 (by decide)
  have h17 : Entails.eval a c578 := derived578 a h
  have h18 : Entails.eval a c1004 := derived1004 a h
  have h19 : Entails.eval a c201 := h 200 (by decide)
  have h20 : Entails.eval a c86 := h 85 (by decide)
  have h21 : Entails.eval a c144 := h 143 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c786 := derived786 a h
  have h24 : Entails.eval a c315 := h 314 (by decide)
  have h25 : Entails.eval a c273 := h 272 (by decide)
  have h26 : Entails.eval a c317 := h 316 (by decide)
  have h27 : Entails.eval a c69 := h 68 (by decide)
  have h28 : Entails.eval a c58 := h 57 (by decide)
  have h29 : Entails.eval a c2 := h 1 (by decide)
  have h30 : Entails.eval a c155 := h 154 (by decide)
  have h31 : Entails.eval a c279 := h 278 (by decide)
  have h32 : Entails.eval a c353 := h 352 (by decide)
  have h33 : Entails.eval a c1119 := derived1119 a h
  have h34 : Entails.eval a c303 := h 302 (by decide)
  have h35 : Entails.eval a c301 := h 300 (by decide)
  have h36 : Entails.eval a c236 := h 235 (by decide)
  have h37 : Entails.eval a c21 := h 20 (by decide)
  have h38 : Entails.eval a c292 := h 291 (by decide)
  have h39 : Entails.eval a c296 := h 295 (by decide)
  have h40 : Entails.eval a c207 := h 206 (by decide)
  have h41 : Entails.eval a c219 := h 218 (by decide)
  have h42 : Entails.eval a c1201 := derived1201 a h
  have h43 : Entails.eval a c101 := h 100 (by decide)
  have h44 : Entails.eval a c64 := h 63 (by decide)
  have h45 : Entails.eval a c77 := h 76 (by decide)
  have h46 : Entails.eval a c26 := h 25 (by decide)
  have h47 : Entails.eval a c193 := h 192 (by decide)
  have h48 : Entails.eval a c355 := h 354 (by decide)
  have h49 : Entails.eval a c343 := h 342 (by decide)
  have h50 : Entails.eval a c183 := h 182 (by decide)
  have h51 : Entails.eval a c393 := h 392 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1204 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨55, by decide⟩, true), (⟨35, by decide⟩, true), (⟨28, by decide⟩, true), (⟨3, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c59, some c117, some c5, some c21, some c920, some c105, some c106, some c41, some c63, some c207, some c168, some c264, some c253, some c15, some c124, some c100, some c185, some c109, some c97, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 57) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c59, c117, c5, c21, c920, c105, c106, c41, c63, c207, c168, c264, c253, c15, c124, c100, c185, c109, c97] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c920 := derived920 a h
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c63 := h 62 (by decide)
  have h9 : Entails.eval a c207 := h 206 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c264 := h 263 (by decide)
  have h12 : Entails.eval a c253 := h 252 (by decide)
  have h13 : Entails.eval a c15 := h 14 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c100 := h 99 (by decide)
  have h16 : Entails.eval a c185 := h 184 (by decide)
  have h17 : Entails.eval a c109 := h 108 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1205 : DefaultClause 57 := directClause [(⟨27, by decide⟩, false), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c117, some c5, some c1192, some c318, some c278, some c59, some c255, some c1204, some c346, some c269, some c63, some c345, some c113, some c207, some c105, some c182, some c264, some c253, some c29, some c95, some c109, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 57) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c268, c117, c5, c1192, c318, c278, c59, c255, c1204, c346, c269, c63, c345, c113, c207, c105, c182, c264, c253, c29, c95, c109] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1192 := derived1192 a h
  have h4 : Entails.eval a c318 := h 317 (by decide)
  have h5 : Entails.eval a c278 := h 277 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c255 := h 254 (by decide)
  have h8 : Entails.eval a c1204 := derived1204 a h
  have h9 : Entails.eval a c346 := h 345 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c63 := h 62 (by decide)
  have h12 : Entails.eval a c345 := h 344 (by decide)
  have h13 : Entails.eval a c113 := h 112 (by decide)
  have h14 : Entails.eval a c207 := h 206 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c182 := h 181 (by decide)
  have h17 : Entails.eval a c264 := h 263 (by decide)
  have h18 : Entails.eval a c253 := h 252 (by decide)
  have h19 : Entails.eval a c29 := h 28 (by decide)
  have h20 : Entails.eval a c95 := h 94 (by decide)
  have h21 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1206 : DefaultClause 57 := directClause [(⟨28, by decide⟩, true), (⟨33, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c269, some c113, some c198, some c207, some c264, some c205, some c124, some c201, some c136, some c149, some c237, some c317, some c286, some c290, some c320, some c367, some c179, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 57) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c117, c269, c113, c198, c207, c264, c205, c124, c201, c136, c149, c237, c317, c286, c290, c320, c367, c179] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c269 := h 268 (by decide)
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c198 := h 197 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c264 := h 263 (by decide)
  have h6 : Entails.eval a c205 := h 204 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c201 := h 200 (by decide)
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c237 := h 236 (by decide)
  have h12 : Entails.eval a c317 := h 316 (by decide)
  have h13 : Entails.eval a c286 := h 285 (by decide)
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c320 := h 319 (by decide)
  have h16 : Entails.eval a c367 := h 366 (by decide)
  have h17 : Entails.eval a c179 := h 178 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1207 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨27, by decide⟩, true), (⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c5, some c346, some c269, some c113, some c198, some c1206, some c52, some c280, some c72, some c24, some c105, some c264, some c29, some c124, some c110, some c201, some c17, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 57) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c117, c5, c346, c269, c113, c198, c1206, c52, c280, c72, c24, c105, c264, c29, c124, c110, c201, c17] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c346 := h 345 (by decide)
  have h3 : Entails.eval a c269 := h 268 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c198 := h 197 (by decide)
  have h6 : Entails.eval a c1206 := derived1206 a h
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c105 := h 104 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c29 := h 28 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c201 := h 200 (by decide)
  have h17 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1208 : DefaultClause 57 := directClause [(⟨28, by decide⟩, false), (⟨16, by decide⟩, true), (⟨8, by decide⟩, true), (⟨37, by decide⟩, false), (⟨21, by decide⟩, true), (⟨19, by decide⟩, false), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c117, some c5, some c52, some c280, some c17, some c24, some c201, some c264, some c124, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 57) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c117, c5, c52, c280, c17, c24, c201, c264, c124] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c117 := h 116 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c280 := h 279 (by decide)
  have h4 : Entails.eval a c17 := h 16 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c201 := h 200 (by decide)
  have h7 : Entails.eval a c264 := h 263 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1209 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨37, by decide⟩, false), (⟨6, by decide⟩, false), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c117, some c5, some c1205, some c1207, some c21, some c106, some c41, some c113, some c198, some c1208, some c207, some c264, some c205, some c124, some c201, some c136, some c149, some c17, some c237, some c317, some c89, some c290, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1209 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 57) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c268, c117, c5, c1205, c1207, c21, c106, c41, c113, c198, c1208, c207, c264, c205, c124, c201, c136, c149, c17, c237, c317, c89, c290] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c1205 := derived1205 a h
  have h4 : Entails.eval a c1207 := derived1207 a h
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c1208 := derived1208 a h
  have h11 : Entails.eval a c207 := h 206 (by decide)
  have h12 : Entails.eval a c264 := h 263 (by decide)
  have h13 : Entails.eval a c205 := h 204 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c201 := h 200 (by decide)
  have h16 : Entails.eval a c136 := h 135 (by decide)
  have h17 : Entails.eval a c149 := h 148 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  have h19 : Entails.eval a c237 := h 236 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  have h21 : Entails.eval a c89 := h 88 (by decide)
  have h22 : Entails.eval a c290 := h 289 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1210 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨32, by decide⟩, false), (⟨20, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨9, by decide⟩, true), (⟨24, by decide⟩, true), (⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨5, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c105, some c106, some c41, some c28, some c37, some c141, some c276, some c168, some c109, some c69, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨32, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p1210 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 57) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c105, c106, c41, c28, c37, c141, c276, c168, c109, c69] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c106 := h 105 (by decide)
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c276 := h 275 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c109 := h 108 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1211 : DefaultClause 57 := directClause [(⟨2, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c110, some c109, some c37, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p1211 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 57) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c110, c109, c37] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c110 := h 109 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1212 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨23, by decide⟩, false), (⟨13, by decide⟩, true), (⟨15, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1203, some c268, some c117, some c5, some c1147, some c26, some c226, some c1209, some c263, some c885, some c131, some c202, some c124, some c264, some c1211, some c9, some c106, some c1210, some c37, some c213, some c52, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p1212 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 57) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c1203, c268, c117, c5, c1147, c26, c226, c1209, c263, c885, c131, c202, c124, c264, c1211, c9, c106, c1210, c37, c213, c52] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c1203 := derived1203 a h
  have h1 : Entails.eval a c268 := h 267 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c1147 := derived1147 a h
  have h5 : Entails.eval a c26 := h 25 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c1209 := derived1209 a h
  have h8 : Entails.eval a c263 := h 262 (by decide)
  have h9 : Entails.eval a c885 := derived885 a h
  have h10 : Entails.eval a c131 := h 130 (by decide)
  have h11 : Entails.eval a c202 := h 201 (by decide)
  have h12 : Entails.eval a c124 := h 123 (by decide)
  have h13 : Entails.eval a c264 := h 263 (by decide)
  have h14 : Entails.eval a c1211 := derived1211 a h
  have h15 : Entails.eval a c9 := h 8 (by decide)
  have h16 : Entails.eval a c106 := h 105 (by decide)
  have h17 : Entails.eval a c1210 := derived1210 a h
  have h18 : Entails.eval a c37 := h 36 (by decide)
  have h19 : Entails.eval a c213 := h 212 (by decide)
  have h20 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1213 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨33, by decide⟩, true), (⟨17, by decide⟩, true), (⟨38, by decide⟩, false), (⟨21, by decide⟩, true), (⟨13, by decide⟩, true), (⟨14, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c124, some c217, some c159, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true))]
def p1213 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 57) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c124, c217, c159] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c124 := h 123 (by decide)
  have h1 : Entails.eval a c217 := h 216 (by decide)
  have h2 : Entails.eval a c159 := h 158 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
#print axioms derived1213

end CochromaticTwenty.Certificates.B16_0_2Enumerating
