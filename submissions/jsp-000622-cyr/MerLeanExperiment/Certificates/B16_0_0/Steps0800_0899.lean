import MerLeanExperiment.Certificates.B16_0_0.Steps0700_0799

/-! Generated from the actual pinned b16_0_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c1194 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨8, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1194 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1193, some c114, some c1191, some c894, some c1060, some c107, some c105, some c98, some c389, some c95, some c104, some c8, some c36, some c189, some c263, some c268, some c13, some c612, some c199, some c205, some c121, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1194 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1194 : lratChecker f1194 p1194 = .success := by decide +kernel
theorem unsat1194 : Unsatisfiable (PosFin 57) f1194 := by
  apply lratCheckerSound f1194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1194
  · intro a ha; simp [p1194] at ha; subst a; trivial
  · exact checked1194
theorem derived1194 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1194 := by
  apply localUnsat_implies_entails f1194 [c1120, c1193, c114, c1191, c894, c1060, c107, c105, c98, c389, c95, c104, c8, c36, c189, c263, c268, c13, c612, c199, c205, c121] c1194 unsat1194 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1193 := derived1193 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c1191 := derived1191 a h
  have h4 : Entails.eval a c894 := derived894 a h
  have h5 : Entails.eval a c1060 := derived1060 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c104 := h 103 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c189 := h 188 (by decide)
  have h15 : Entails.eval a c263 := h 262 (by decide)
  have h16 : Entails.eval a c268 := h 267 (by decide)
  have h17 : Entails.eval a c13 := h 12 (by decide)
  have h18 : Entails.eval a c612 := derived612 a h
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c205 := h 204 (by decide)
  have h21 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1195 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1195 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1060, some c894, some c1191, some c107, some c105, some c98, some c389, some c95, some c104, some c1193, some c114, some c133, some c75, some c1194, some c267, some c236, some c3, some c189, some c17, some c19, some c169, some c199, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1195 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1195 : lratChecker f1195 p1195 = .success := by decide +kernel
theorem unsat1195 : Unsatisfiable (PosFin 57) f1195 := by
  apply lratCheckerSound f1195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1195
  · intro a ha; simp [p1195] at ha; subst a; trivial
  · exact checked1195
theorem derived1195 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1195 := by
  apply localUnsat_implies_entails f1195 [c1120, c1060, c894, c1191, c107, c105, c98, c389, c95, c104, c1193, c114, c133, c75, c1194, c267, c236, c3, c189, c17, c19, c169, c199] c1195 unsat1195 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c894 := derived894 a h
  have h3 : Entails.eval a c1191 := derived1191 a h
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c105 := h 104 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c389 := h 388 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c1193 := derived1193 a h
  have h11 : Entails.eval a c114 := h 113 (by decide)
  have h12 : Entails.eval a c133 := h 132 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c1194 := derived1194 a h
  have h15 : Entails.eval a c267 := h 266 (by decide)
  have h16 : Entails.eval a c236 := h 235 (by decide)
  have h17 : Entails.eval a c3 := h 2 (by decide)
  have h18 : Entails.eval a c189 := h 188 (by decide)
  have h19 : Entails.eval a c17 := h 16 (by decide)
  have h20 : Entails.eval a c19 := h 18 (by decide)
  have h21 : Entails.eval a c169 := h 168 (by decide)
  have h22 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1196 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1196 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c894, some c253, some c269, some c267, some c33, some c3, some c110, some c95, some c107, some c585, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1196 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1196 : lratChecker f1196 p1196 = .success := by decide +kernel
theorem unsat1196 : Unsatisfiable (PosFin 57) f1196 := by
  apply lratCheckerSound f1196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1196
  · intro a ha; simp [p1196] at ha; subst a; trivial
  · exact checked1196
theorem derived1196 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1196 := by
  apply localUnsat_implies_entails f1196 [c1060, c1195, c111, c894, c253, c269, c267, c33, c3, c110, c95, c107, c585] c1196 unsat1196 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c894 := derived894 a h
  have h4 : Entails.eval a c253 := h 252 (by decide)
  have h5 : Entails.eval a c269 := h 268 (by decide)
  have h6 : Entails.eval a c267 := h 266 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c107 := h 106 (by decide)
  have h12 : Entails.eval a c585 := derived585 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1197 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1197 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c353, some c358, some c20, some c263, some c32, some c225, some c112, some c359, some c64, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1197 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1197 : lratChecker f1197 p1197 = .success := by decide +kernel
theorem unsat1197 : Unsatisfiable (PosFin 57) f1197 := by
  apply lratCheckerSound f1197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1197
  · intro a ha; simp [p1197] at ha; subst a; trivial
  · exact checked1197
theorem derived1197 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1197 := by
  apply localUnsat_implies_entails f1197 [c22, c353, c358, c20, c263, c32, c225, c112, c359, c64] c1197 unsat1197 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c358 := h 357 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c263 := h 262 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c225 := h 224 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c359 := h 358 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1198 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨7, by decide⟩, false), (⟨2, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1198 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1196, some c1060, some c1195, some c111, some c1197, some c57, some c389, some c391, some c97, some c112, some c96, some c32, some c251, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1198 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1198 : lratChecker f1198 p1198 = .success := by decide +kernel
theorem unsat1198 : Unsatisfiable (PosFin 57) f1198 := by
  apply lratCheckerSound f1198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1198
  · intro a ha; simp [p1198] at ha; subst a; trivial
  · exact checked1198
theorem derived1198 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1198 := by
  apply localUnsat_implies_entails f1198 [c1196, c1060, c1195, c111, c1197, c57, c389, c391, c97, c112, c96, c32, c251] c1198 unsat1198 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1195 := derived1195 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1197 := derived1197 a h
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c389 := h 388 (by decide)
  have h7 : Entails.eval a c391 := h 390 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c251 := h 250 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1199 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1199 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1196, some c1060, some c1195, some c111, some c1120, some c1, some c20, some c198, some c152, some c58, some c389, some c189, some c57, some c517, some c120, some c354, some c142, some c322, some c272, some c280, some c206, some c225, some c268, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1199 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1199 : lratChecker f1199 p1199 = .success := by decide +kernel
theorem unsat1199 : Unsatisfiable (PosFin 57) f1199 := by
  apply lratCheckerSound f1199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1199
  · intro a ha; simp [p1199] at ha; subst a; trivial
  · exact checked1199
theorem derived1199 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1199 := by
  apply localUnsat_implies_entails f1199 [c1196, c1060, c1195, c111, c1120, c1, c20, c198, c152, c58, c389, c189, c57, c517, c120, c354, c142, c322, c272, c280, c206, c225, c268] c1199 unsat1199 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1195 := derived1195 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1120 := derived1120 a h
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c198 := h 197 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c389 := h 388 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c517 := derived517 a h
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c354 := h 353 (by decide)
  have h16 : Entails.eval a c142 := h 141 (by decide)
  have h17 : Entails.eval a c322 := h 321 (by decide)
  have h18 : Entails.eval a c272 := h 271 (by decide)
  have h19 : Entails.eval a c280 := h 279 (by decide)
  have h20 : Entails.eval a c206 := h 205 (by decide)
  have h21 : Entails.eval a c225 := h 224 (by decide)
  have h22 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1200 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1200 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c894, some c1199, some c262, some c1198, some c98, some c95, some c389, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1200 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1200 : lratChecker f1200 p1200 = .success := by decide +kernel
theorem unsat1200 : Unsatisfiable (PosFin 57) f1200 := by
  apply lratCheckerSound f1200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1200
  · intro a ha; simp [p1200] at ha; subst a; trivial
  · exact checked1200
theorem derived1200 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1200 := by
  apply localUnsat_implies_entails f1200 [c1060, c1195, c111, c894, c1199, c262, c1198, c98, c95, c389] c1200 unsat1200 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c894 := derived894 a h
  have h4 : Entails.eval a c1199 := derived1199 a h
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c1198 := derived1198 a h
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c389 := h 388 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1201 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨5, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1201 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c389, some c391, some c97, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1201 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1201 : lratChecker f1201 p1201 = .success := by decide +kernel
theorem unsat1201 : Unsatisfiable (PosFin 57) f1201 := by
  apply lratCheckerSound f1201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1201
  · intro a ha; simp [p1201] at ha; subst a; trivial
  · exact checked1201
theorem derived1201 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1201 := by
  apply localUnsat_implies_entails f1201 [c1060, c1195, c111, c389, c391, c97] c1201 unsat1201 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c389 := h 388 (by decide)
  have h4 : Entails.eval a c391 := h 390 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1202 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨2, by decide⟩, false), (⟨11, by decide⟩, false), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1202 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1196, some c1195, some c1120, some c1060, some c517, some c120, some c47, some c133, some c560, some c83, some c122, some c169, some c228, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1202 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1202 : lratChecker f1202 p1202 = .success := by decide +kernel
theorem unsat1202 : Unsatisfiable (PosFin 57) f1202 := by
  apply lratCheckerSound f1202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1202
  · intro a ha; simp [p1202] at ha; subst a; trivial
  · exact checked1202
theorem derived1202 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1202 := by
  apply localUnsat_implies_entails f1202 [c1196, c1195, c1120, c1060, c517, c120, c47, c133, c560, c83, c122, c169, c228] c1202 unsat1202 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c1120 := derived1120 a h
  have h3 : Entails.eval a c1060 := derived1060 a h
  have h4 : Entails.eval a c517 := derived517 a h
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c133 := h 132 (by decide)
  have h8 : Entails.eval a c560 := derived560 a h
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c122 := h 121 (by decide)
  have h11 : Entails.eval a c169 := h 168 (by decide)
  have h12 : Entails.eval a c228 := h 227 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1203 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1203 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c894, some c1060, some c1195, some c111, some c1200, some c1202, some c189, some c98, some c110, some c1201, some c1196, some c22, some c33, some c268, some c161, some c225, some c1197, some c843, some c345, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1203 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1203 : lratChecker f1203 p1203 = .success := by decide +kernel
theorem unsat1203 : Unsatisfiable (PosFin 57) f1203 := by
  apply lratCheckerSound f1203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1203
  · intro a ha; simp [p1203] at ha; subst a; trivial
  · exact checked1203
theorem derived1203 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1203 := by
  apply localUnsat_implies_entails f1203 [c894, c1060, c1195, c111, c1200, c1202, c189, c98, c110, c1201, c1196, c22, c33, c268, c161, c225, c1197, c843, c345] c1203 unsat1203 (by rfl) a
  have h0 : Entails.eval a c894 := derived894 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1195 := derived1195 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c1200 := derived1200 a h
  have h5 : Entails.eval a c1202 := derived1202 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c1201 := derived1201 a h
  have h10 : Entails.eval a c1196 := derived1196 a h
  have h11 : Entails.eval a c22 := h 21 (by decide)
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c268 := h 267 (by decide)
  have h14 : Entails.eval a c161 := h 160 (by decide)
  have h15 : Entails.eval a c225 := h 224 (by decide)
  have h16 : Entails.eval a c1197 := derived1197 a h
  have h17 : Entails.eval a c843 := derived843 a h
  have h18 : Entails.eval a c345 := h 344 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1204 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1204 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c1200, some c110, some c1202, some c189, some c97, some c193, some c1203, some c58, some c9, some c262, some c152, some c20, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1204 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1204 : lratChecker f1204 p1204 = .success := by decide +kernel
theorem unsat1204 : Unsatisfiable (PosFin 57) f1204 := by
  apply lratCheckerSound f1204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1204
  · intro a ha; simp [p1204] at ha; subst a; trivial
  · exact checked1204
theorem derived1204 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1204 := by
  apply localUnsat_implies_entails f1204 [c1060, c1195, c111, c1200, c110, c1202, c189, c97, c193, c1203, c58, c9, c262, c152, c20] c1204 unsat1204 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1200 := derived1200 a h
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1202 := derived1202 a h
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c193 := h 192 (by decide)
  have h9 : Entails.eval a c1203 := derived1203 a h
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c262 := h 261 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1205 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨11, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1205 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c14, some c1201, some c193, some c344, some c97, some c392, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1205 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1205 : lratChecker f1205 p1205 = .success := by decide +kernel
theorem unsat1205 : Unsatisfiable (PosFin 57) f1205 := by
  apply lratCheckerSound f1205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1205
  · intro a ha; simp [p1205] at ha; subst a; trivial
  · exact checked1205
theorem derived1205 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1205 := by
  apply localUnsat_implies_entails f1205 [c1060, c1195, c111, c14, c1201, c193, c344, c97, c392] c1205 unsat1205 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c1201 := derived1201 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c344 := h 343 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c392 := h 391 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1206 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨34, by decide⟩, true), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1206 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c1204, some c3, some c262, some c20, some c1, some c894, some c110, some c57, some c389, some c98, some c112, some c96, some c13, some c251, some c153, some c23, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1206 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1206 : lratChecker f1206 p1206 = .success := by decide +kernel
theorem unsat1206 : Unsatisfiable (PosFin 57) f1206 := by
  apply lratCheckerSound f1206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1206
  · intro a ha; simp [p1206] at ha; subst a; trivial
  · exact checked1206
theorem derived1206 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1206 := by
  apply localUnsat_implies_entails f1206 [c1060, c1195, c111, c1204, c3, c262, c20, c1, c894, c110, c57, c389, c98, c112, c96, c13, c251, c153, c23] c1206 unsat1206 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c894 := derived894 a h
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c389 := h 388 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c112 := h 111 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  have h15 : Entails.eval a c13 := h 12 (by decide)
  have h16 : Entails.eval a c251 := h 250 (by decide)
  have h17 : Entails.eval a c153 := h 152 (by decide)
  have h18 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1207 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1207 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c1204, some c3, some c262, some c20, some c1, some c894, some c353, some c355, some c1206, some c1201, some c28, some c57, some c1175, some c345, some c344, some c268, some c224, some c155, some c392, some c936, some c97, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1207 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked1207 : lratChecker f1207 p1207 = .success := by decide +kernel
theorem unsat1207 : Unsatisfiable (PosFin 57) f1207 := by
  apply lratCheckerSound f1207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1207
  · intro a ha; simp [p1207] at ha; subst a; trivial
  · exact checked1207
theorem derived1207 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1207 := by
  apply localUnsat_implies_entails f1207 [c1060, c1195, c111, c1204, c3, c262, c20, c1, c894, c353, c355, c1206, c1201, c28, c57, c1175, c345, c344, c268, c224, c155, c392, c936, c97] c1207 unsat1207 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c1204 := derived1204 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c262 := h 261 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c894 := derived894 a h
  have h9 : Entails.eval a c353 := h 352 (by decide)
  have h10 : Entails.eval a c355 := h 354 (by decide)
  have h11 : Entails.eval a c1206 := derived1206 a h
  have h12 : Entails.eval a c1201 := derived1201 a h
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c1175 := derived1175 a h
  have h16 : Entails.eval a c345 := h 344 (by decide)
  have h17 : Entails.eval a c344 := h 343 (by decide)
  have h18 : Entails.eval a c268 := h 267 (by decide)
  have h19 : Entails.eval a c224 := h 223 (by decide)
  have h20 : Entails.eval a c155 := h 154 (by decide)
  have h21 : Entails.eval a c392 := h 391 (by decide)
  have h22 : Entails.eval a c936 := derived936 a h
  have h23 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1208 : DefaultClause 57 := directClause [(⟨34, by decide⟩, true), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1208 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c345, some c344, some c357, some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1208 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1208 : lratChecker f1208 p1208 = .success := by decide +kernel
theorem unsat1208 : Unsatisfiable (PosFin 57) f1208 := by
  apply lratCheckerSound f1208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1208
  · intro a ha; simp [p1208] at ha; subst a; trivial
  · exact checked1208
theorem derived1208 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1208 := by
  apply localUnsat_implies_entails f1208 [c345, c344, c357] c1208 unsat1208 (by rfl) a
  have h0 : Entails.eval a c345 := h 344 (by decide)
  have h1 : Entails.eval a c344 := h 343 (by decide)
  have h2 : Entails.eval a c357 := h 356 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1209 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨34, by decide⟩, false), (⟨35, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1209 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c20, some c354, some c28, some c69, some c268, some c360, some c225, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1209 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1209 : lratChecker f1209 p1209 = .success := by decide +kernel
theorem unsat1209 : Unsatisfiable (PosFin 57) f1209 := by
  apply lratCheckerSound f1209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1209
  · intro a ha; simp [p1209] at ha; subst a; trivial
  · exact checked1209
theorem derived1209 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1209 := by
  apply localUnsat_implies_entails f1209 [c20, c354, c28, c69, c268, c360, c225] c1209 unsat1209 (by rfl) a
  have h0 : Entails.eval a c20 := h 19 (by decide)
  have h1 : Entails.eval a c354 := h 353 (by decide)
  have h2 : Entails.eval a c28 := h 27 (by decide)
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c360 := h 359 (by decide)
  have h6 : Entails.eval a c225 := h 224 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1210 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1210 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1196, some c1060, some c1195, some c111, some c894, some c1204, some c3, some c262, some c20, some c1207, some c58, some c389, some c392, some c1208, some c354, some c68, some c1209, some c110, some c112, some c95, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1210 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1210 : lratChecker f1210 p1210 = .success := by decide +kernel
theorem unsat1210 : Unsatisfiable (PosFin 57) f1210 := by
  apply lratCheckerSound f1210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1210
  · intro a ha; simp [p1210] at ha; subst a; trivial
  · exact checked1210
theorem derived1210 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1210 := by
  apply localUnsat_implies_entails f1210 [c1196, c1060, c1195, c111, c894, c1204, c3, c262, c20, c1207, c58, c389, c392, c1208, c354, c68, c1209, c110, c112, c95] c1210 unsat1210 (by rfl) a
  have h0 : Entails.eval a c1196 := derived1196 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1195 := derived1195 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c894 := derived894 a h
  have h5 : Entails.eval a c1204 := derived1204 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c262 := h 261 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c1207 := derived1207 a h
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c389 := h 388 (by decide)
  have h12 : Entails.eval a c392 := h 391 (by decide)
  have h13 : Entails.eval a c1208 := derived1208 a h
  have h14 : Entails.eval a c354 := h 353 (by decide)
  have h15 : Entails.eval a c68 := h 67 (by decide)
  have h16 : Entails.eval a c1209 := derived1209 a h
  have h17 : Entails.eval a c110 := h 109 (by decide)
  have h18 : Entails.eval a c112 := h 111 (by decide)
  have h19 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1211 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨35, by decide⟩, false), (⟨54, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1211 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1208, some c353, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1211 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1211 : lratChecker f1211 p1211 = .success := by decide +kernel
theorem unsat1211 : Unsatisfiable (PosFin 57) f1211 := by
  apply lratCheckerSound f1211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1211
  · intro a ha; simp [p1211] at ha; subst a; trivial
  · exact checked1211
theorem derived1211 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1211 := by
  apply localUnsat_implies_entails f1211 [c1208, c353] c1211 unsat1211 (by rfl) a
  have h0 : Entails.eval a c1208 := derived1208 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1212 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨4, by decide⟩, true), (⟨18, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1212 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c263, some c262, some c32, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1212 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1212 : lratChecker f1212 p1212 = .success := by decide +kernel
theorem unsat1212 : Unsatisfiable (PosFin 57) f1212 := by
  apply lratCheckerSound f1212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1212
  · intro a ha; simp [p1212] at ha; subst a; trivial
  · exact checked1212
theorem derived1212 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1212 := by
  apply localUnsat_implies_entails f1212 [c263, c262, c32] c1212 unsat1212 (by rfl) a
  have h0 : Entails.eval a c263 := h 262 (by decide)
  have h1 : Entails.eval a c262 := h 261 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1213 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1213 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c1195, some c111, some c894, some c1196, some c1210, some c107, some c98, some c389, some c392, some c95, some c110, some c104, some c1000, some c1211, some c1212, some c218, some c358, some c361, some c344, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1213 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1213 : lratChecker f1213 p1213 = .success := by decide +kernel
theorem unsat1213 : Unsatisfiable (PosFin 57) f1213 := by
  apply lratCheckerSound f1213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1213
  · intro a ha; simp [p1213] at ha; subst a; trivial
  · exact checked1213
theorem derived1213 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1213 := by
  apply localUnsat_implies_entails f1213 [c1060, c1195, c111, c894, c1196, c1210, c107, c98, c389, c392, c95, c110, c104, c1000, c1211, c1212, c218, c358, c361, c344] c1213 unsat1213 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c111 := h 110 (by decide)
  have h3 : Entails.eval a c894 := derived894 a h
  have h4 : Entails.eval a c1196 := derived1196 a h
  have h5 : Entails.eval a c1210 := derived1210 a h
  have h6 : Entails.eval a c107 := h 106 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c389 := h 388 (by decide)
  have h9 : Entails.eval a c392 := h 391 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c1000 := derived1000 a h
  have h14 : Entails.eval a c1211 := derived1211 a h
  have h15 : Entails.eval a c1212 := derived1212 a h
  have h16 : Entails.eval a c218 := h 217 (by decide)
  have h17 : Entails.eval a c358 := h 357 (by decide)
  have h18 : Entails.eval a c361 := h 360 (by decide)
  have h19 : Entails.eval a c344 := h 343 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1214 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨1, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1214 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1060, some c107, some c1120, some c1213, some c2, some c1195, some c111, some c34, some c583, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1214 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1214 : lratChecker f1214 p1214 = .success := by decide +kernel
theorem unsat1214 : Unsatisfiable (PosFin 57) f1214 := by
  apply lratCheckerSound f1214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1214
  · intro a ha; simp [p1214] at ha; subst a; trivial
  · exact checked1214
theorem derived1214 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1214 := by
  apply localUnsat_implies_entails f1214 [c1060, c107, c1120, c1213, c2, c1195, c111, c34, c583] c1214 unsat1214 (by rfl) a
  have h0 : Entails.eval a c1060 := derived1060 a h
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c1120 := derived1120 a h
  have h3 : Entails.eval a c1213 := derived1213 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1195 := derived1195 a h
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c583 := derived583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1215 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1215 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1213, some c2, some c1195, some c114, some c47, some c110, some c1060, some c111, some c894, some c107, some c98, some c1214, some c255, some c120, some c189, some c612, some c14, some c13, some c205, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1215 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1215 : lratChecker f1215 p1215 = .success := by decide +kernel
theorem unsat1215 : Unsatisfiable (PosFin 57) f1215 := by
  apply lratCheckerSound f1215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1215
  · intro a ha; simp [p1215] at ha; subst a; trivial
  · exact checked1215
theorem derived1215 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1215 := by
  apply localUnsat_implies_entails f1215 [c1120, c1213, c2, c1195, c114, c47, c110, c1060, c111, c894, c107, c98, c1214, c255, c120, c189, c612, c14, c13, c205] c1215 unsat1215 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1195 := derived1195 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c894 := derived894 a h
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c1214 := derived1214 a h
  have h13 : Entails.eval a c255 := h 254 (by decide)
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c189 := h 188 (by decide)
  have h16 : Entails.eval a c612 := derived612 a h
  have h17 : Entails.eval a c14 := h 13 (by decide)
  have h18 : Entails.eval a c13 := h 12 (by decide)
  have h19 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1216 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨33, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1216 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1195, some c1120, some c1213, some c2, some c110, some c1201, some c894, some c1215, some c20, some c56, some c64, some c982, some c59, some c23, some c247, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1216 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1216 : lratChecker f1216 p1216 = .success := by decide +kernel
theorem unsat1216 : Unsatisfiable (PosFin 57) f1216 := by
  apply lratCheckerSound f1216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1216
  · intro a ha; simp [p1216] at ha; subst a; trivial
  · exact checked1216
theorem derived1216 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1216 := by
  apply localUnsat_implies_entails f1216 [c1195, c1120, c1213, c2, c110, c1201, c894, c1215, c20, c56, c64, c982, c59, c23, c247] c1216 unsat1216 (by rfl) a
  have h0 : Entails.eval a c1195 := derived1195 a h
  have h1 : Entails.eval a c1120 := derived1120 a h
  have h2 : Entails.eval a c1213 := derived1213 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1201 := derived1201 a h
  have h6 : Entails.eval a c894 := derived894 a h
  have h7 : Entails.eval a c1215 := derived1215 a h
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c64 := h 63 (by decide)
  have h11 : Entails.eval a c982 := derived982 a h
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c247 := h 246 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1217 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨16, by decide⟩, false), (⟨33, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1217 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1213, some c2, some c1216, some c104, some c56, some c20, some c1060, some c1195, some c111, some c246, some c189, some c3, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1217 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked1217 : lratChecker f1217 p1217 = .success := by decide +kernel
theorem unsat1217 : Unsatisfiable (PosFin 57) f1217 := by
  apply lratCheckerSound f1217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1217
  · intro a ha; simp [p1217] at ha; subst a; trivial
  · exact checked1217
theorem derived1217 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1217 := by
  apply localUnsat_implies_entails f1217 [c1120, c1213, c2, c1216, c104, c56, c20, c1060, c1195, c111, c246, c189, c3] c1217 unsat1217 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1216 := derived1216 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c1195 := derived1195 a h
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c189 := h 188 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1218 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, true), (⟨33, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1218 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1213, some c124, some c114, some c2, some c1216, some c45, some c104, some c1195, some c47, some c110, some c1060, some c111, some c894, some c120, some c216, some c1217, some c98, some c97, some c54, some c193, some c9, some c200, some c199, some c147, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1218 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1218 : lratChecker f1218 p1218 = .success := by decide +kernel
theorem unsat1218 : Unsatisfiable (PosFin 57) f1218 := by
  apply lratCheckerSound f1218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1218
  · intro a ha; simp [p1218] at ha; subst a; trivial
  · exact checked1218
theorem derived1218 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1218 := by
  apply localUnsat_implies_entails f1218 [c1120, c1213, c124, c114, c2, c1216, c45, c104, c1195, c47, c110, c1060, c111, c894, c120, c216, c1217, c98, c97, c54, c193, c9, c200, c199, c147] c1218 unsat1218 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c114 := h 113 (by decide)
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c1216 := derived1216 a h
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c1195 := derived1195 a h
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c110 := h 109 (by decide)
  have h11 : Entails.eval a c1060 := derived1060 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c894 := derived894 a h
  have h14 : Entails.eval a c120 := h 119 (by decide)
  have h15 : Entails.eval a c216 := h 215 (by decide)
  have h16 : Entails.eval a c1217 := derived1217 a h
  have h17 : Entails.eval a c98 := h 97 (by decide)
  have h18 : Entails.eval a c97 := h 96 (by decide)
  have h19 : Entails.eval a c54 := h 53 (by decide)
  have h20 : Entails.eval a c193 := h 192 (by decide)
  have h21 : Entails.eval a c9 := h 8 (by decide)
  have h22 : Entails.eval a c200 := h 199 (by decide)
  have h23 : Entails.eval a c199 := h 198 (by decide)
  have h24 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1219 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨24, by decide⟩, false), (⟨15, by decide⟩, false), (⟨28, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1219 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1213, some c2, some c1195, some c114, some c47, some c110, some c259, some c5, some c193, some c205, some c148, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1219 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1219 : lratChecker f1219 p1219 = .success := by decide +kernel
theorem unsat1219 : Unsatisfiable (PosFin 57) f1219 := by
  apply lratCheckerSound f1219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1219
  · intro a ha; simp [p1219] at ha; subst a; trivial
  · exact checked1219
theorem derived1219 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1219 := by
  apply localUnsat_implies_entails f1219 [c1120, c1213, c2, c1195, c114, c47, c110, c259, c5, c193, c205, c148] c1219 unsat1219 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1195 := derived1195 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c259 := h 258 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c193 := h 192 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1220 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨33, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1220 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1213, some c2, some c1216, some c104, some c56, some c20, some c114, some c45, some c1195, some c47, some c110, some c1060, some c111, some c124, some c1218, some c1219, some c97, some c246, some c1217, some c3, some c148, some c180, some c205, some c9, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1220 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1220 : lratChecker f1220 p1220 = .success := by decide +kernel
theorem unsat1220 : Unsatisfiable (PosFin 57) f1220 := by
  apply lratCheckerSound f1220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1220
  · intro a ha; simp [p1220] at ha; subst a; trivial
  · exact checked1220
theorem derived1220 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1220 := by
  apply localUnsat_implies_entails f1220 [c1120, c1213, c2, c1216, c104, c56, c20, c114, c45, c1195, c47, c110, c1060, c111, c124, c1218, c1219, c97, c246, c1217, c3, c148, c180, c205, c9] c1220 unsat1220 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1216 := derived1216 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c45 := h 44 (by decide)
  have h9 : Entails.eval a c1195 := derived1195 a h
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c1060 := derived1060 a h
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c124 := h 123 (by decide)
  have h15 : Entails.eval a c1218 := derived1218 a h
  have h16 : Entails.eval a c1219 := derived1219 a h
  have h17 : Entails.eval a c97 := h 96 (by decide)
  have h18 : Entails.eval a c246 := h 245 (by decide)
  have h19 : Entails.eval a c1217 := derived1217 a h
  have h20 : Entails.eval a c3 := h 2 (by decide)
  have h21 : Entails.eval a c148 := h 147 (by decide)
  have h22 : Entails.eval a c180 := h 179 (by decide)
  have h23 : Entails.eval a c205 := h 204 (by decide)
  have h24 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1221 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1221 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1195, some c1120, some c1213, some c2, some c110, some c1201, some c114, some c47, some c1060, some c111, some c894, some c1216, some c104, some c45, some c20, some c64, some c982, some c1220, some c265, some c266, some c657, some c214, some c116, some c123, some c224, some c502, some c160, some c281, some c14, some c507, some c205, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1221 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked1221 : lratChecker f1221 p1221 = .success := by decide +kernel
theorem unsat1221 : Unsatisfiable (PosFin 57) f1221 := by
  apply lratCheckerSound f1221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1221
  · intro a ha; simp [p1221] at ha; subst a; trivial
  · exact checked1221
theorem derived1221 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1221 := by
  apply localUnsat_implies_entails f1221 [c1195, c1120, c1213, c2, c110, c1201, c114, c47, c1060, c111, c894, c1216, c104, c45, c20, c64, c982, c1220, c265, c266, c657, c214, c116, c123, c224, c502, c160, c281, c14, c507, c205] c1221 unsat1221 (by rfl) a
  have h0 : Entails.eval a c1195 := derived1195 a h
  have h1 : Entails.eval a c1120 := derived1120 a h
  have h2 : Entails.eval a c1213 := derived1213 a h
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  have h5 : Entails.eval a c1201 := derived1201 a h
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c1060 := derived1060 a h
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c894 := derived894 a h
  have h11 : Entails.eval a c1216 := derived1216 a h
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c20 := h 19 (by decide)
  have h15 : Entails.eval a c64 := h 63 (by decide)
  have h16 : Entails.eval a c982 := derived982 a h
  have h17 : Entails.eval a c1220 := derived1220 a h
  have h18 : Entails.eval a c265 := h 264 (by decide)
  have h19 : Entails.eval a c266 := h 265 (by decide)
  have h20 : Entails.eval a c657 := derived657 a h
  have h21 : Entails.eval a c214 := h 213 (by decide)
  have h22 : Entails.eval a c116 := h 115 (by decide)
  have h23 : Entails.eval a c123 := h 122 (by decide)
  have h24 : Entails.eval a c224 := h 223 (by decide)
  have h25 : Entails.eval a c502 := derived502 a h
  have h26 : Entails.eval a c160 := h 159 (by decide)
  have h27 : Entails.eval a c281 := h 280 (by decide)
  have h28 : Entails.eval a c14 := h 13 (by decide)
  have h29 : Entails.eval a c507 := derived507 a h
  have h30 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1222 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1222 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1221, some c1195, some c1120, some c1213, some c2, some c110, some c1201, some c1060, some c111, some c894, some c502, some c1211, some c353, some c355, some c261, some c219, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1222 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1222 : lratChecker f1222 p1222 = .success := by decide +kernel
theorem unsat1222 : Unsatisfiable (PosFin 57) f1222 := by
  apply lratCheckerSound f1222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1222
  · intro a ha; simp [p1222] at ha; subst a; trivial
  · exact checked1222
theorem derived1222 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1222 := by
  apply localUnsat_implies_entails f1222 [c1221, c1195, c1120, c1213, c2, c110, c1201, c1060, c111, c894, c502, c1211, c353, c355, c261, c219] c1222 unsat1222 (by rfl) a
  have h0 : Entails.eval a c1221 := derived1221 a h
  have h1 : Entails.eval a c1195 := derived1195 a h
  have h2 : Entails.eval a c1120 := derived1120 a h
  have h3 : Entails.eval a c1213 := derived1213 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c1201 := derived1201 a h
  have h7 : Entails.eval a c1060 := derived1060 a h
  have h8 : Entails.eval a c111 := h 110 (by decide)
  have h9 : Entails.eval a c894 := derived894 a h
  have h10 : Entails.eval a c502 := derived502 a h
  have h11 : Entails.eval a c1211 := derived1211 a h
  have h12 : Entails.eval a c353 := h 352 (by decide)
  have h13 : Entails.eval a c355 := h 354 (by decide)
  have h14 : Entails.eval a c261 := h 260 (by decide)
  have h15 : Entails.eval a c219 := h 218 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1223 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1223 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1120, some c1213, some c2, some c1195, some c114, some c47, some c1222, some c120, some c1221, some c110, some c1201, some c1060, some c111, some c894, some c1211, some c353, some c355, some c392, some c1205, some c98, some c97, some c152, some c107, some c193, some c9, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1223 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1223 : lratChecker f1223 p1223 = .success := by decide +kernel
theorem unsat1223 : Unsatisfiable (PosFin 57) f1223 := by
  apply lratCheckerSound f1223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1223
  · intro a ha; simp [p1223] at ha; subst a; trivial
  · exact checked1223
theorem derived1223 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1223 := by
  apply localUnsat_implies_entails f1223 [c1120, c1213, c2, c1195, c114, c47, c1222, c120, c1221, c110, c1201, c1060, c111, c894, c1211, c353, c355, c392, c1205, c98, c97, c152, c107, c193, c9] c1223 unsat1223 (by rfl) a
  have h0 : Entails.eval a c1120 := derived1120 a h
  have h1 : Entails.eval a c1213 := derived1213 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c1195 := derived1195 a h
  have h4 : Entails.eval a c114 := h 113 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c1222 := derived1222 a h
  have h7 : Entails.eval a c120 := h 119 (by decide)
  have h8 : Entails.eval a c1221 := derived1221 a h
  have h9 : Entails.eval a c110 := h 109 (by decide)
  have h10 : Entails.eval a c1201 := derived1201 a h
  have h11 : Entails.eval a c1060 := derived1060 a h
  have h12 : Entails.eval a c111 := h 110 (by decide)
  have h13 : Entails.eval a c894 := derived894 a h
  have h14 : Entails.eval a c1211 := derived1211 a h
  have h15 : Entails.eval a c353 := h 352 (by decide)
  have h16 : Entails.eval a c355 := h 354 (by decide)
  have h17 : Entails.eval a c392 := h 391 (by decide)
  have h18 : Entails.eval a c1205 := derived1205 a h
  have h19 : Entails.eval a c98 := h 97 (by decide)
  have h20 : Entails.eval a c97 := h 96 (by decide)
  have h21 : Entails.eval a c152 := h 151 (by decide)
  have h22 : Entails.eval a c107 := h 106 (by decide)
  have h23 : Entails.eval a c193 := h 192 (by decide)
  have h24 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1224 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1224 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c894, some c1060, some c1120, some c1195, some c111, some c1213, some c2, some c114, some c110, some c47, some c1201, some c1221, some c1222, some c120, some c1223, some c22, some c58, some c1000, some c392, some c189, some c104, some c1208, some c14, some c272, some c193, some c207, some c92, some c246, some (DefaultClause.unit (⟨56, by decide⟩, true))]
def p1224 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1224 : lratChecker f1224 p1224 = .success := by decide +kernel
theorem unsat1224 : Unsatisfiable (PosFin 57) f1224 := by
  apply lratCheckerSound f1224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1224
  · intro a ha; simp [p1224] at ha; subst a; trivial
  · exact checked1224
theorem derived1224 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1224 := by
  apply localUnsat_implies_entails f1224 [c894, c1060, c1120, c1195, c111, c1213, c2, c114, c110, c47, c1201, c1221, c1222, c120, c1223, c22, c58, c1000, c392, c189, c104, c1208, c14, c272, c193, c207, c92, c246] c1224 unsat1224 (by rfl) a
  have h0 : Entails.eval a c894 := derived894 a h
  have h1 : Entails.eval a c1060 := derived1060 a h
  have h2 : Entails.eval a c1120 := derived1120 a h
  have h3 : Entails.eval a c1195 := derived1195 a h
  have h4 : Entails.eval a c111 := h 110 (by decide)
  have h5 : Entails.eval a c1213 := derived1213 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c1201 := derived1201 a h
  have h11 : Entails.eval a c1221 := derived1221 a h
  have h12 : Entails.eval a c1222 := derived1222 a h
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c1223 := derived1223 a h
  have h15 : Entails.eval a c22 := h 21 (by decide)
  have h16 : Entails.eval a c58 := h 57 (by decide)
  have h17 : Entails.eval a c1000 := derived1000 a h
  have h18 : Entails.eval a c392 := h 391 (by decide)
  have h19 : Entails.eval a c189 := h 188 (by decide)
  have h20 : Entails.eval a c104 := h 103 (by decide)
  have h21 : Entails.eval a c1208 := derived1208 a h
  have h22 : Entails.eval a c14 := h 13 (by decide)
  have h23 : Entails.eval a c272 := h 271 (by decide)
  have h24 : Entails.eval a c193 := h 192 (by decide)
  have h25 : Entails.eval a c207 := h 206 (by decide)
  have h26 : Entails.eval a c92 := h 91 (by decide)
  have h27 : Entails.eval a c246 := h 245 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1225 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨1, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨36, by decide⟩, true), (⟨34, by decide⟩, false), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1225 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c28, some c69, some c360, some c225, some c1209, some c271, some c124, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1225 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1225 : lratChecker f1225 p1225 = .success := by decide +kernel
theorem unsat1225 : Unsatisfiable (PosFin 57) f1225 := by
  apply lratCheckerSound f1225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1225
  · intro a ha; simp [p1225] at ha; subst a; trivial
  · exact checked1225
theorem derived1225 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1225 := by
  apply localUnsat_implies_entails f1225 [c28, c69, c360, c225, c1209, c271, c124] c1225 unsat1225 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c225 := h 224 (by decide)
  have h4 : Entails.eval a c1209 := derived1209 a h
  have h5 : Entails.eval a c271 := h 270 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1226 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨1, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨36, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1226 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c28, some c1225, some c270, some c544, some c224, some c271, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1226 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1226 : lratChecker f1226 p1226 = .success := by decide +kernel
theorem unsat1226 : Unsatisfiable (PosFin 57) f1226 := by
  apply lratCheckerSound f1226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1226
  · intro a ha; simp [p1226] at ha; subst a; trivial
  · exact checked1226
theorem derived1226 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1226 := by
  apply localUnsat_implies_entails f1226 [c22, c28, c1225, c270, c544, c224, c271] c1226 unsat1226 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c1225 := derived1225 a h
  have h3 : Entails.eval a c270 := h 269 (by decide)
  have h4 : Entails.eval a c544 := derived544 a h
  have h5 : Entails.eval a c224 := h 223 (by decide)
  have h6 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1227 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1227 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c262, some c264, some c124, some c224, some c265, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p1227 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1227 : lratChecker f1227 p1227 = .success := by decide +kernel
theorem unsat1227 : Unsatisfiable (PosFin 57) f1227 := by
  apply lratCheckerSound f1227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1227
  · intro a ha; simp [p1227] at ha; subst a; trivial
  · exact checked1227
theorem derived1227 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1227 := by
  apply localUnsat_implies_entails f1227 [c262, c264, c124, c224, c265] c1227 unsat1227 (by rfl) a
  have h0 : Entails.eval a c262 := h 261 (by decide)
  have h1 : Entails.eval a c264 := h 263 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c224 := h 223 (by decide)
  have h4 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1228 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨15, by decide⟩, true), (⟨10, by decide⟩, true), (⟨5, by decide⟩, true), (⟨36, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1228 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c22, some c1227, some c1, some c28, some c1225, some c1226, some c269, some c270, some c198, some c123, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1228 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1228 : lratChecker f1228 p1228 = .success := by decide +kernel
theorem unsat1228 : Unsatisfiable (PosFin 57) f1228 := by
  apply lratCheckerSound f1228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1228
  · intro a ha; simp [p1228] at ha; subst a; trivial
  · exact checked1228
theorem derived1228 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1228 := by
  apply localUnsat_implies_entails f1228 [c22, c1227, c1, c28, c1225, c1226, c269, c270, c198, c123] c1228 unsat1228 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c1227 := derived1227 a h
  have h2 : Entails.eval a c1 := h 0 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c1225 := derived1225 a h
  have h5 : Entails.eval a c1226 := derived1226 a h
  have h6 : Entails.eval a c269 := h 268 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c198 := h 197 (by decide)
  have h9 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1229 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1229 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c107, some c104, some c95, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1229 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1229 : lratChecker f1229 p1229 = .success := by decide +kernel
theorem unsat1229 : Unsatisfiable (PosFin 57) f1229 := by
  apply lratCheckerSound f1229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1229
  · intro a ha; simp [p1229] at ha; subst a; trivial
  · exact checked1229
theorem derived1229 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1229 := by
  apply localUnsat_implies_entails f1229 [c107, c104, c95] c1229 unsat1229 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1230 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1230 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c63, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p1230 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1230 : lratChecker f1230 p1230 = .success := by decide +kernel
theorem unsat1230 : Unsatisfiable (PosFin 57) f1230 := by
  apply lratCheckerSound f1230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1230
  · intro a ha; simp [p1230] at ha; subst a; trivial
  · exact checked1230
theorem derived1230 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1230 := by
  apply localUnsat_implies_entails f1230 [c1224, c63] c1230 unsat1230 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1231 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨1, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1231 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c93, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1231 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1231 : lratChecker f1231 p1231 = .success := by decide +kernel
theorem unsat1231 : Unsatisfiable (PosFin 57) f1231 := by
  apply lratCheckerSound f1231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1231
  · intro a ha; simp [p1231] at ha; subst a; trivial
  · exact checked1231
theorem derived1231 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1231 := by
  apply localUnsat_implies_entails f1231 [c1224, c93] c1231 unsat1231 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1232 : DefaultClause 57 := directClause [(⟨8, by decide⟩, true), (⟨4, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1232 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c100, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1232 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1232 : lratChecker f1232 p1232 = .success := by decide +kernel
theorem unsat1232 : Unsatisfiable (PosFin 57) f1232 := by
  apply lratCheckerSound f1232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1232
  · intro a ha; simp [p1232] at ha; subst a; trivial
  · exact checked1232
theorem derived1232 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1232 := by
  apply localUnsat_implies_entails f1232 [c1224, c100] c1232 unsat1232 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1233 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1233 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c102, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1233 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1233 : lratChecker f1233 p1233 = .success := by decide +kernel
theorem unsat1233 : Unsatisfiable (PosFin 57) f1233 := by
  apply lratCheckerSound f1233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1233
  · intro a ha; simp [p1233] at ha; subst a; trivial
  · exact checked1233
theorem derived1233 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1233 := by
  apply localUnsat_implies_entails f1233 [c1224, c102] c1233 unsat1233 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1234 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨40, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1234 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c343, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1234 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1234 : lratChecker f1234 p1234 = .success := by decide +kernel
theorem unsat1234 : Unsatisfiable (PosFin 57) f1234 := by
  apply lratCheckerSound f1234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1234
  · intro a ha; simp [p1234] at ha; subst a; trivial
  · exact checked1234
theorem derived1234 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1234 := by
  apply localUnsat_implies_entails f1234 [c1224, c343] c1234 unsat1234 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c343 := h 342 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1235 : DefaultClause 57 := directClause [(⟨40, by decide⟩, true), (⟨52, by decide⟩, true), (⟨36, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1235 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c350, some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false))]
def p1235 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1235 : lratChecker f1235 p1235 = .success := by decide +kernel
theorem unsat1235 : Unsatisfiable (PosFin 57) f1235 := by
  apply lratCheckerSound f1235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1235
  · intro a ha; simp [p1235] at ha; subst a; trivial
  · exact checked1235
theorem derived1235 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1235 := by
  apply localUnsat_implies_entails f1235 [c1224, c350] c1235 unsat1235 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c350 := h 349 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1236 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨40, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1236 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c352, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1236 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1236 : lratChecker f1236 p1236 = .success := by decide +kernel
theorem unsat1236 : Unsatisfiable (PosFin 57) f1236 := by
  apply lratCheckerSound f1236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1236
  · intro a ha; simp [p1236] at ha; subst a; trivial
  · exact checked1236
theorem derived1236 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1236 := by
  apply localUnsat_implies_entails f1236 [c1224, c352] c1236 unsat1236 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c352 := h 351 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1237 : DefaultClause 57 := directClause [(⟨41, by decide⟩, true), (⟨48, by decide⟩, true), (⟨49, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1237 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c364, some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, false))]
def p1237 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1237 : lratChecker f1237 p1237 = .success := by decide +kernel
theorem unsat1237 : Unsatisfiable (PosFin 57) f1237 := by
  apply lratCheckerSound f1237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1237
  · intro a ha; simp [p1237] at ha; subst a; trivial
  · exact checked1237
theorem derived1237 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1237 := by
  apply localUnsat_implies_entails f1237 [c1224, c364] c1237 unsat1237 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c364 := h 363 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1238 : DefaultClause 57 := directClause [(⟨44, by decide⟩, true), (⟨48, by decide⟩, true), (⟨52, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1238 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c371, some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false))]
def p1238 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1238 : lratChecker f1238 p1238 = .success := by decide +kernel
theorem unsat1238 : Unsatisfiable (PosFin 57) f1238 := by
  apply lratCheckerSound f1238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1238
  · intro a ha; simp [p1238] at ha; subst a; trivial
  · exact checked1238
theorem derived1238 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1238 := by
  apply localUnsat_implies_entails f1238 [c1224, c371] c1238 unsat1238 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c371 := h 370 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1239 : DefaultClause 57 := directClause [(⟨47, by decide⟩, true), (⟨48, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1239 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1224, some c373, some (DefaultClause.unit (⟨47, by decide⟩, false)), some (DefaultClause.unit (⟨48, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1239 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked1239 : lratChecker f1239 p1239 = .success := by decide +kernel
theorem unsat1239 : Unsatisfiable (PosFin 57) f1239 := by
  apply lratCheckerSound f1239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1239
  · intro a ha; simp [p1239] at ha; subst a; trivial
  · exact checked1239
theorem derived1239 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1239 := by
  apply localUnsat_implies_entails f1239 [c1224, c373] c1239 unsat1239 (by rfl) a
  have h0 : Entails.eval a c1224 := derived1224 a h
  have h1 : Entails.eval a c373 := h 372 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c1240 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨37, by decide⟩, false), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨34, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1240 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c158, some c9, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1240 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1240 : lratChecker f1240 p1240 = .success := by decide +kernel
theorem unsat1240 : Unsatisfiable (PosFin 57) f1240 := by
  apply lratCheckerSound f1240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1240
  · intro a ha; simp [p1240] at ha; subst a; trivial
  · exact checked1240
theorem derived1240 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1240 := by
  apply localUnsat_implies_entails f1240 [c151, c158, c9] c1240 unsat1240 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1241 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1241 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c69, some c360, some c1236, some c1240, some c1228, some c155, some c164, some c9, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1241 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1241 : lratChecker f1241 p1241 = .success := by decide +kernel
theorem unsat1241 : Unsatisfiable (PosFin 57) f1241 := by
  apply lratCheckerSound f1241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1241
  · intro a ha; simp [p1241] at ha; subst a; trivial
  · exact checked1241
theorem derived1241 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1241 := by
  apply localUnsat_implies_entails f1241 [c354, c69, c360, c1236, c1240, c1228, c155, c164, c9] c1241 unsat1241 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c69 := h 68 (by decide)
  have h2 : Entails.eval a c360 := h 359 (by decide)
  have h3 : Entails.eval a c1236 := derived1236 a h
  have h4 : Entails.eval a c1240 := derived1240 a h
  have h5 : Entails.eval a c1228 := derived1228 a h
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c164 := h 163 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1242 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1242 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c112, some c95, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1242 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1242 : lratChecker f1242 p1242 = .success := by decide +kernel
theorem unsat1242 : Unsatisfiable (PosFin 57) f1242 := by
  apply lratCheckerSound f1242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1242
  · intro a ha; simp [p1242] at ha; subst a; trivial
  · exact checked1242
theorem derived1242 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1242 := by
  apply localUnsat_implies_entails f1242 [c109, c112, c95] c1242 unsat1242 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1243 : DefaultClause 57 := directClause [(⟨34, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1243 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c354, some c68, some c1242, some c1241, some c104, some c106, some c95, some (DefaultClause.unit (⟨34, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1243 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1243 : lratChecker f1243 p1243 = .success := by decide +kernel
theorem unsat1243 : Unsatisfiable (PosFin 57) f1243 := by
  apply lratCheckerSound f1243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1243
  · intro a ha; simp [p1243] at ha; subst a; trivial
  · exact checked1243
theorem derived1243 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1243 := by
  apply localUnsat_implies_entails f1243 [c354, c68, c1242, c1241, c104, c106, c95] c1243 unsat1243 (by rfl) a
  have h0 : Entails.eval a c354 := h 353 (by decide)
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c1242 := derived1242 a h
  have h3 : Entails.eval a c1241 := derived1241 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c106 := h 105 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1244 : DefaultClause 57 := directClause [(⟨38, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1244 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c58, some c22, some c1243, some c57, some c345, some c344, some c1074, some c356, some c254, some c68, some c224, some c219, some c1242, some c104, some c268, some c28, some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1244 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1244 : lratChecker f1244 p1244 = .success := by decide +kernel
theorem unsat1244 : Unsatisfiable (PosFin 57) f1244 := by
  apply lratCheckerSound f1244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1244
  · intro a ha; simp [p1244] at ha; subst a; trivial
  · exact checked1244
theorem derived1244 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1244 := by
  apply localUnsat_implies_entails f1244 [c58, c22, c1243, c57, c345, c344, c1074, c356, c254, c68, c224, c219, c1242, c104, c268, c28] c1244 unsat1244 (by rfl) a
  have h0 : Entails.eval a c58 := h 57 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c1243 := derived1243 a h
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c344 := h 343 (by decide)
  have h6 : Entails.eval a c1074 := derived1074 a h
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c254 := h 253 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c219 := h 218 (by decide)
  have h12 : Entails.eval a c1242 := derived1242 a h
  have h13 : Entails.eval a c104 := h 103 (by decide)
  have h14 : Entails.eval a c268 := h 267 (by decide)
  have h15 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1245 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨50, by decide⟩, true), (⟨33, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1245 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1244, some c986, some c357, some c1242, some c1236, some c345, some c69, some c360, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1245 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1245 : lratChecker f1245 p1245 = .success := by decide +kernel
theorem unsat1245 : Unsatisfiable (PosFin 57) f1245 := by
  apply lratCheckerSound f1245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1245
  · intro a ha; simp [p1245] at ha; subst a; trivial
  · exact checked1245
theorem derived1245 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1245 := by
  apply localUnsat_implies_entails f1245 [c1244, c986, c357, c1242, c1236, c345, c69, c360] c1245 unsat1245 (by rfl) a
  have h0 : Entails.eval a c1244 := derived1244 a h
  have h1 : Entails.eval a c986 := derived986 a h
  have h2 : Entails.eval a c357 := h 356 (by decide)
  have h3 : Entails.eval a c1242 := derived1242 a h
  have h4 : Entails.eval a c1236 := derived1236 a h
  have h5 : Entails.eval a c345 := h 344 (by decide)
  have h6 : Entails.eval a c69 := h 68 (by decide)
  have h7 : Entails.eval a c360 := h 359 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1246 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨21, by decide⟩, false), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1246 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c224, some c219, some c268, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p1246 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1246 : lratChecker f1246 p1246 = .success := by decide +kernel
theorem unsat1246 : Unsatisfiable (PosFin 57) f1246 := by
  apply lratCheckerSound f1246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1246
  · intro a ha; simp [p1246] at ha; subst a; trivial
  · exact checked1246
theorem derived1246 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1246 := by
  apply localUnsat_implies_entails f1246 [c224, c219, c268] c1246 unsat1246 (by rfl) a
  have h0 : Entails.eval a c224 := h 223 (by decide)
  have h1 : Entails.eval a c219 := h 218 (by decide)
  have h2 : Entails.eval a c268 := h 267 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1247 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1247 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c355, some c353, some c1, some c28, some c152, some c155, some c3, some c14, some c165, some c1246, some c270, some c8, some c120, some c131, some c47, some c282, some c286, some c271, some c146, some c134, some c129, some c276, some c326, some c197, some c289, some c114, some c133, some c235, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1247 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked1247 : lratChecker f1247 p1247 = .success := by decide +kernel
theorem unsat1247 : Unsatisfiable (PosFin 57) f1247 := by
  apply lratCheckerSound f1247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1247
  · intro a ha; simp [p1247] at ha; subst a; trivial
  · exact checked1247
theorem derived1247 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1247 := by
  apply localUnsat_implies_entails f1247 [c356, c355, c353, c1, c28, c152, c155, c3, c14, c165, c1246, c270, c8, c120, c131, c47, c282, c286, c271, c146, c134, c129, c276, c326, c197, c289, c114, c133, c235] c1247 unsat1247 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c1 := h 0 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c14 := h 13 (by decide)
  have h9 : Entails.eval a c165 := h 164 (by decide)
  have h10 : Entails.eval a c1246 := derived1246 a h
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c120 := h 119 (by decide)
  have h14 : Entails.eval a c131 := h 130 (by decide)
  have h15 : Entails.eval a c47 := h 46 (by decide)
  have h16 : Entails.eval a c282 := h 281 (by decide)
  have h17 : Entails.eval a c286 := h 285 (by decide)
  have h18 : Entails.eval a c271 := h 270 (by decide)
  have h19 : Entails.eval a c146 := h 145 (by decide)
  have h20 : Entails.eval a c134 := h 133 (by decide)
  have h21 : Entails.eval a c129 := h 128 (by decide)
  have h22 : Entails.eval a c276 := h 275 (by decide)
  have h23 : Entails.eval a c326 := h 325 (by decide)
  have h24 : Entails.eval a c197 := h 196 (by decide)
  have h25 : Entails.eval a c289 := h 288 (by decide)
  have h26 : Entails.eval a c114 := h 113 (by decide)
  have h27 : Entails.eval a c133 := h 132 (by decide)
  have h28 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1248 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨37, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1248 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c356, some c355, some c353, some c1247, some c1074, some c3, some c33, some c152, some c161, some c1246, some c9, some c266, some c164, some c7, some c131, some c119, some c269, some c51, some c276, some c124, some c202, some c116, some c135, some c642, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1248 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1248 : lratChecker f1248 p1248 = .success := by decide +kernel
theorem unsat1248 : Unsatisfiable (PosFin 57) f1248 := by
  apply lratCheckerSound f1248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1248
  · intro a ha; simp [p1248] at ha; subst a; trivial
  · exact checked1248
theorem derived1248 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1248 := by
  apply localUnsat_implies_entails f1248 [c104, c356, c355, c353, c1247, c1074, c3, c33, c152, c161, c1246, c9, c266, c164, c7, c131, c119, c269, c51, c276, c124, c202, c116, c135, c642] c1248 unsat1248 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c1247 := derived1247 a h
  have h5 : Entails.eval a c1074 := derived1074 a h
  have h6 : Entails.eval a c3 := h 2 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  have h10 : Entails.eval a c1246 := derived1246 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c164 := h 163 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c131 := h 130 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c269 := h 268 (by decide)
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c276 := h 275 (by decide)
  have h20 : Entails.eval a c124 := h 123 (by decide)
  have h21 : Entails.eval a c202 := h 201 (by decide)
  have h22 : Entails.eval a c116 := h 115 (by decide)
  have h23 : Entails.eval a c135 := h 134 (by decide)
  have h24 : Entails.eval a c642 := derived642 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1249 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨37, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1249 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c1248, some c1235, some c104, some c355, some c353, some c1074, some c3, some c33, some c152, some c1246, some c9, some c266, some c248, some c164, some c7, some c119, some c792, some c51, some c190, some c256, some c116, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1249 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1249 : lratChecker f1249 p1249 = .success := by decide +kernel
theorem unsat1249 : Unsatisfiable (PosFin 57) f1249 := by
  apply lratCheckerSound f1249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1249
  · intro a ha; simp [p1249] at ha; subst a; trivial
  · exact checked1249
theorem derived1249 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1249 := by
  apply localUnsat_implies_entails f1249 [c356, c1248, c1235, c104, c355, c353, c1074, c3, c33, c152, c1246, c9, c266, c248, c164, c7, c119, c792, c51, c190, c256, c116] c1249 unsat1249 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c1248 := derived1248 a h
  have h2 : Entails.eval a c1235 := derived1235 a h
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c353 := h 352 (by decide)
  have h6 : Entails.eval a c1074 := derived1074 a h
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c1246 := derived1246 a h
  have h11 : Entails.eval a c9 := h 8 (by decide)
  have h12 : Entails.eval a c266 := h 265 (by decide)
  have h13 : Entails.eval a c248 := h 247 (by decide)
  have h14 : Entails.eval a c164 := h 163 (by decide)
  have h15 : Entails.eval a c7 := h 6 (by decide)
  have h16 : Entails.eval a c119 := h 118 (by decide)
  have h17 : Entails.eval a c792 := derived792 a h
  have h18 : Entails.eval a c51 := h 50 (by decide)
  have h19 : Entails.eval a c190 := h 189 (by decide)
  have h20 : Entails.eval a c256 := h 255 (by decide)
  have h21 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1250 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1250 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c356, some c355, some c353, some c1248, some c1235, some c1249, some c1, some c28, some c152, some c1246, some c3, some c270, some c254, some c225, some c97, some c256, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1250 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked1250 : lratChecker f1250 p1250 = .success := by decide +kernel
theorem unsat1250 : Unsatisfiable (PosFin 57) f1250 := by
  apply lratCheckerSound f1250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1250
  · intro a ha; simp [p1250] at ha; subst a; trivial
  · exact checked1250
theorem derived1250 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1250 := by
  apply localUnsat_implies_entails f1250 [c104, c356, c355, c353, c1248, c1235, c1249, c1, c28, c152, c1246, c3, c270, c254, c225, c97, c256] c1250 unsat1250 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c356 := h 355 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c1248 := derived1248 a h
  have h5 : Entails.eval a c1235 := derived1235 a h
  have h6 : Entails.eval a c1249 := derived1249 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c152 := h 151 (by decide)
  have h10 : Entails.eval a c1246 := derived1246 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c270 := h 269 (by decide)
  have h13 : Entails.eval a c254 := h 253 (by decide)
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c97 := h 96 (by decide)
  have h16 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1251 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨24, by decide⟩, true), (⟨15, by decide⟩, true), (⟨21, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1251 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c268, some c271, some c124, some c131, some c1083, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1251 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1251 : lratChecker f1251 p1251 = .success := by decide +kernel
theorem unsat1251 : Unsatisfiable (PosFin 57) f1251 := by
  apply lratCheckerSound f1251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1251
  · intro a ha; simp [p1251] at ha; subst a; trivial
  · exact checked1251
theorem derived1251 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1251 := by
  apply localUnsat_implies_entails f1251 [c268, c271, c124, c131, c1083] c1251 unsat1251 (by rfl) a
  have h0 : Entails.eval a c268 := h 267 (by decide)
  have h1 : Entails.eval a c271 := h 270 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c1083 := derived1083 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1252 : DefaultClause 57 := directClause [(⟨23, by decide⟩, true), (⟨40, by decide⟩, false), (⟨20, by decide⟩, true), (⟨8, by decide⟩, false), (⟨24, by decide⟩, true), (⟨7, by decide⟩, false), (⟨13, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false), (⟨35, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1252 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c119, some c131, some c51, some c54, some c203, some c214, some c124, some c47, some c282, some c552, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true))]
def p1252 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1252 : lratChecker f1252 p1252 = .success := by decide +kernel
theorem unsat1252 : Unsatisfiable (PosFin 57) f1252 := by
  apply lratCheckerSound f1252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1252
  · intro a ha; simp [p1252] at ha; subst a; trivial
  · exact checked1252
theorem derived1252 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1252 := by
  apply localUnsat_implies_entails f1252 [c119, c131, c51, c54, c203, c214, c124, c47, c282, c552] c1252 unsat1252 (by rfl) a
  have h0 : Entails.eval a c119 := h 118 (by decide)
  have h1 : Entails.eval a c131 := h 130 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c203 := h 202 (by decide)
  have h5 : Entails.eval a c214 := h 213 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c282 := h 281 (by decide)
  have h9 : Entails.eval a c552 := derived552 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1253 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨44, by decide⟩, true), (⟨46, by decide⟩, true), (⟨7, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1253 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c51, some c54, some c296, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨44, by decide⟩, false)), some (DefaultClause.unit (⟨46, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p1253 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1253 : lratChecker f1253 p1253 = .success := by decide +kernel
theorem unsat1253 : Unsatisfiable (PosFin 57) f1253 := by
  apply lratCheckerSound f1253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1253
  · intro a ha; simp [p1253] at ha; subst a; trivial
  · exact checked1253
theorem derived1253 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1253 := by
  apply localUnsat_implies_entails f1253 [c51, c54, c296] c1253 unsat1253 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c296 := h 295 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1254 : DefaultClause 57 := directClause [(⟨10, by decide⟩, true), (⟨18, by decide⟩, false), (⟨23, by decide⟩, false), (⟨7, by decide⟩, false), (⟨19, by decide⟩, false), (⟨15, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1254 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c104, some c270, some c29, some c415, some c243, some c87, some c1253, some c143, some c146, some c47, some c315, some c207, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p1254 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1254 : lratChecker f1254 p1254 = .success := by decide +kernel
theorem unsat1254 : Unsatisfiable (PosFin 57) f1254 := by
  apply lratCheckerSound f1254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1254
  · intro a ha; simp [p1254] at ha; subst a; trivial
  · exact checked1254
theorem derived1254 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1254 := by
  apply localUnsat_implies_entails f1254 [c104, c270, c29, c415, c243, c87, c1253, c143, c146, c47, c315, c207] c1254 unsat1254 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c270 := h 269 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c415 := derived415 a h
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c87 := h 86 (by decide)
  have h6 : Entails.eval a c1253 := derived1253 a h
  have h7 : Entails.eval a c143 := h 142 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c315 := h 314 (by decide)
  have h11 : Entails.eval a c207 := h 206 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1255 : DefaultClause 57 := directClause [(⟨10, by decide⟩, false), (⟨20, by decide⟩, true), (⟨24, by decide⟩, true), (⟨13, by decide⟩, false), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1255 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1083, some c202, some c129, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1255 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1255 : lratChecker f1255 p1255 = .success := by decide +kernel
theorem unsat1255 : Unsatisfiable (PosFin 57) f1255 := by
  apply lratCheckerSound f1255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1255
  · intro a ha; simp [p1255] at ha; subst a; trivial
  · exact checked1255
theorem derived1255 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1255 := by
  apply localUnsat_implies_entails f1255 [c1083, c202, c129] c1255 unsat1255 (by rfl) a
  have h0 : Entails.eval a c1083 := derived1083 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1256 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨39, by decide⟩, false), (⟨2, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1256 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c355, some c356, some c1246, some c104, some c1, some c152, some c155, some c3, some c14, some c15, some c270, some c29, some c1251, some c225, some c1252, some c1255, some c1254, some c114, some c47, some c45, some c214, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1256 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked1256 : lratChecker f1256 p1256 = .success := by decide +kernel
theorem unsat1256 : Unsatisfiable (PosFin 57) f1256 := by
  apply lratCheckerSound f1256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1256
  · intro a ha; simp [p1256] at ha; subst a; trivial
  · exact checked1256
theorem derived1256 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1256 := by
  apply localUnsat_implies_entails f1256 [c353, c355, c356, c1246, c104, c1, c152, c155, c3, c14, c15, c270, c29, c1251, c225, c1252, c1255, c1254, c114, c47, c45, c214] c1256 unsat1256 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c356 := h 355 (by decide)
  have h3 : Entails.eval a c1246 := derived1246 a h
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c155 := h 154 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  have h11 : Entails.eval a c270 := h 269 (by decide)
  have h12 : Entails.eval a c29 := h 28 (by decide)
  have h13 : Entails.eval a c1251 := derived1251 a h
  have h14 : Entails.eval a c225 := h 224 (by decide)
  have h15 : Entails.eval a c1252 := derived1252 a h
  have h16 : Entails.eval a c1255 := derived1255 a h
  have h17 : Entails.eval a c1254 := derived1254 a h
  have h18 : Entails.eval a c114 := h 113 (by decide)
  have h19 : Entails.eval a c47 := h 46 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1257 : DefaultClause 57 := directClause [(⟨31, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, false), (⟨22, by decide⟩, false), (⟨6, by decide⟩, false), (⟨39, by decide⟩, false), (⟨54, by decide⟩, false), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1257 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c276, some c54, some c132, some c420, some c137, some c326, some c329, some c188, some c369, some (DefaultClause.unit (⟨31, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1257 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1257 : lratChecker f1257 p1257 = .success := by decide +kernel
theorem unsat1257 : Unsatisfiable (PosFin 57) f1257 := by
  apply lratCheckerSound f1257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1257
  · intro a ha; simp [p1257] at ha; subst a; trivial
  · exact checked1257
theorem derived1257 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1257 := by
  apply localUnsat_implies_entails f1257 [c152, c276, c54, c132, c420, c137, c326, c329, c188, c369] c1257 unsat1257 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c276 := h 275 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c420 := derived420 a h
  have h5 : Entails.eval a c137 := h 136 (by decide)
  have h6 : Entails.eval a c326 := h 325 (by decide)
  have h7 : Entails.eval a c329 := h 328 (by decide)
  have h8 : Entails.eval a c188 := h 187 (by decide)
  have h9 : Entails.eval a c369 := h 368 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1258 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1258 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c353, some c345, some c356, some c57, some c355, some c1211, some c104, some c1250, some c73, some c24, some c1246, some c1256, some c1074, some c266, some c248, some c3, some c34, some c1231, some c152, some c1257, some c212, some c273, some c132, some c329, some c1239, some c366, some c83, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1258 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1258 : lratChecker f1258 p1258 = .success := by decide +kernel
theorem unsat1258 : Unsatisfiable (PosFin 57) f1258 := by
  apply lratCheckerSound f1258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1258
  · intro a ha; simp [p1258] at ha; subst a; trivial
  · exact checked1258
theorem derived1258 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1258 := by
  apply localUnsat_implies_entails f1258 [c1245, c353, c345, c356, c57, c355, c1211, c104, c1250, c73, c24, c1246, c1256, c1074, c266, c248, c3, c34, c1231, c152, c1257, c212, c273, c132, c329, c1239, c366, c83] c1258 unsat1258 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  have h5 : Entails.eval a c355 := h 354 (by decide)
  have h6 : Entails.eval a c1211 := derived1211 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c1250 := derived1250 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c24 := h 23 (by decide)
  have h11 : Entails.eval a c1246 := derived1246 a h
  have h12 : Entails.eval a c1256 := derived1256 a h
  have h13 : Entails.eval a c1074 := derived1074 a h
  have h14 : Entails.eval a c266 := h 265 (by decide)
  have h15 : Entails.eval a c248 := h 247 (by decide)
  have h16 : Entails.eval a c3 := h 2 (by decide)
  have h17 : Entails.eval a c34 := h 33 (by decide)
  have h18 : Entails.eval a c1231 := derived1231 a h
  have h19 : Entails.eval a c152 := h 151 (by decide)
  have h20 : Entails.eval a c1257 := derived1257 a h
  have h21 : Entails.eval a c212 := h 211 (by decide)
  have h22 : Entails.eval a c273 := h 272 (by decide)
  have h23 : Entails.eval a c132 := h 131 (by decide)
  have h24 : Entails.eval a c329 := h 328 (by decide)
  have h25 : Entails.eval a c1239 := derived1239 a h
  have h26 : Entails.eval a c366 := h 365 (by decide)
  have h27 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1259 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨9, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨36, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1259 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c1074, some c248, some c33, some c92, some c1006, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1259 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked1259 : lratChecker f1259 p1259 = .success := by decide +kernel
theorem unsat1259 : Unsatisfiable (PosFin 57) f1259 := by
  apply lratCheckerSound f1259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1259
  · intro a ha; simp [p1259] at ha; subst a; trivial
  · exact checked1259
theorem derived1259 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1259 := by
  apply localUnsat_implies_entails f1259 [c1, c1074, c248, c33, c92, c1006] c1259 unsat1259 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c1074 := derived1074 a h
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c1006 := derived1006 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1260 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨54, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1260 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c98, some c34, some c254, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1260 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1260 : lratChecker f1260 p1260 = .success := by decide +kernel
theorem unsat1260 : Unsatisfiable (PosFin 57) f1260 := by
  apply lratCheckerSound f1260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1260
  · intro a ha; simp [p1260] at ha; subst a; trivial
  · exact checked1260
theorem derived1260 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1260 := by
  apply localUnsat_implies_entails f1260 [c98, c34, c254] c1260 unsat1260 (by rfl) a
  have h0 : Entails.eval a c98 := h 97 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c254 := h 253 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1261 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨22, by decide⟩, false), (⟨52, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1261 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c1002, some c254, some c97, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1261 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked1261 : lratChecker f1261 p1261 = .success := by decide +kernel
theorem unsat1261 : Unsatisfiable (PosFin 57) f1261 := by
  apply lratCheckerSound f1261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1261
  · intro a ha; simp [p1261] at ha; subst a; trivial
  · exact checked1261
theorem derived1261 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1261 := by
  apply localUnsat_implies_entails f1261 [c3, c1002, c254, c97] c1261 unsat1261 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c1002 := derived1002 a h
  have h2 : Entails.eval a c254 := h 253 (by decide)
  have h3 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c1262 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1262 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c353, some c345, some c356, some c355, some c1258, some c71, some c59, some c57, some c1211, some c1261, some c152, some c1259, some c107, some c1233, some c98, some c1260, some c254, some c583, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1262 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked1262 : lratChecker f1262 p1262 = .success := by decide +kernel
theorem unsat1262 : Unsatisfiable (PosFin 57) f1262 := by
  apply lratCheckerSound f1262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1262
  · intro a ha; simp [p1262] at ha; subst a; trivial
  · exact checked1262
theorem derived1262 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1262 := by
  apply localUnsat_implies_entails f1262 [c1245, c353, c345, c356, c355, c1258, c71, c59, c57, c1211, c1261, c152, c1259, c107, c1233, c98, c1260, c254, c583] c1262 unsat1262 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c1258 := derived1258 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c57 := h 56 (by decide)
  have h9 : Entails.eval a c1211 := derived1211 a h
  have h10 : Entails.eval a c1261 := derived1261 a h
  have h11 : Entails.eval a c152 := h 151 (by decide)
  have h12 : Entails.eval a c1259 := derived1259 a h
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c1233 := derived1233 a h
  have h15 : Entails.eval a c98 := h 97 (by decide)
  have h16 : Entails.eval a c1260 := derived1260 a h
  have h17 : Entails.eval a c254 := h 253 (by decide)
  have h18 : Entails.eval a c583 := derived583 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1263 : DefaultClause 57 := directClause [(⟨5, by decide⟩, true), (⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1263 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c353, some c345, some c356, some c355, some c1211, some c1258, some c23, some c71, some c1262, some c219, some c1246, some c263, some c24, some c5, some c1160, some c28, some c164, some c138, some c107, some c612, some c329, some c98, some c152, some c132, some c188, some c42, some c118, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1263 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked1263 : lratChecker f1263 p1263 = .success := by decide +kernel
theorem unsat1263 : Unsatisfiable (PosFin 57) f1263 := by
  apply lratCheckerSound f1263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1263
  · intro a ha; simp [p1263] at ha; subst a; trivial
  · exact checked1263
theorem derived1263 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1263 := by
  apply localUnsat_implies_entails f1263 [c1245, c353, c345, c356, c355, c1211, c1258, c23, c71, c1262, c219, c1246, c263, c24, c5, c1160, c28, c164, c138, c107, c612, c329, c98, c152, c132, c188, c42, c118] c1263 unsat1263 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c345 := h 344 (by decide)
  have h3 : Entails.eval a c356 := h 355 (by decide)
  have h4 : Entails.eval a c355 := h 354 (by decide)
  have h5 : Entails.eval a c1211 := derived1211 a h
  have h6 : Entails.eval a c1258 := derived1258 a h
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c1262 := derived1262 a h
  have h10 : Entails.eval a c219 := h 218 (by decide)
  have h11 : Entails.eval a c1246 := derived1246 a h
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c24 := h 23 (by decide)
  have h14 : Entails.eval a c5 := h 4 (by decide)
  have h15 : Entails.eval a c1160 := derived1160 a h
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c164 := h 163 (by decide)
  have h18 : Entails.eval a c138 := h 137 (by decide)
  have h19 : Entails.eval a c107 := h 106 (by decide)
  have h20 : Entails.eval a c612 := derived612 a h
  have h21 : Entails.eval a c329 := h 328 (by decide)
  have h22 : Entails.eval a c98 := h 97 (by decide)
  have h23 : Entails.eval a c152 := h 151 (by decide)
  have h24 : Entails.eval a c132 := h 131 (by decide)
  have h25 : Entails.eval a c188 := h 187 (by decide)
  have h26 : Entails.eval a c42 := h 41 (by decide)
  have h27 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1264 : DefaultClause 57 := directClause [(⟨50, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1264 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1245, some c353, some c355, some c57, some c345, some c356, some c1263, some c109, some c110, some c59, some c23, some c71, some c1233, some c107, some c1231, some c247, some c1, some c152, some c181, some c13, some (DefaultClause.unit (⟨50, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1264 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1264 : lratChecker f1264 p1264 = .success := by decide +kernel
theorem unsat1264 : Unsatisfiable (PosFin 57) f1264 := by
  apply lratCheckerSound f1264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1264
  · intro a ha; simp [p1264] at ha; subst a; trivial
  · exact checked1264
theorem derived1264 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1264 := by
  apply localUnsat_implies_entails f1264 [c1245, c353, c355, c57, c345, c356, c1263, c109, c110, c59, c23, c71, c1233, c107, c1231, c247, c1, c152, c181, c13] c1264 unsat1264 (by rfl) a
  have h0 : Entails.eval a c1245 := derived1245 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c345 := h 344 (by decide)
  have h5 : Entails.eval a c356 := h 355 (by decide)
  have h6 : Entails.eval a c1263 := derived1263 a h
  have h7 : Entails.eval a c109 := h 108 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c71 := h 70 (by decide)
  have h12 : Entails.eval a c1233 := derived1233 a h
  have h13 : Entails.eval a c107 := h 106 (by decide)
  have h14 : Entails.eval a c1231 := derived1231 a h
  have h15 : Entails.eval a c247 := h 246 (by decide)
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c152 := h 151 (by decide)
  have h18 : Entails.eval a c181 := h 180 (by decide)
  have h19 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1265 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨36, by decide⟩, true), (⟨9, by decide⟩, false), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1265 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c3, some c59, some c23, some c71, some c13, some c251, some c197, some c199, some c21, some c219, some c114, some c612, some c110, some c270, some c1190, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1265 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1265 : lratChecker f1265 p1265 = .success := by decide +kernel
theorem unsat1265 : Unsatisfiable (PosFin 57) f1265 := by
  apply lratCheckerSound f1265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1265
  · intro a ha; simp [p1265] at ha; subst a; trivial
  · exact checked1265
theorem derived1265 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1265 := by
  apply localUnsat_implies_entails f1265 [c3, c59, c23, c71, c13, c251, c197, c199, c21, c219, c114, c612, c110, c270, c1190] c1265 unsat1265 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c59 := h 58 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c251 := h 250 (by decide)
  have h6 : Entails.eval a c197 := h 196 (by decide)
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c612 := derived612 a h
  have h12 : Entails.eval a c110 := h 109 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c1190 := derived1190 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1266 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨19, by decide⟩, false), (⟨5, by decide⟩, false), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1266 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c109, some c112, some c21, some c98, some c250, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1266 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1266 : lratChecker f1266 p1266 = .success := by decide +kernel
theorem unsat1266 : Unsatisfiable (PosFin 57) f1266 := by
  apply lratCheckerSound f1266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1266
  · intro a ha; simp [p1266] at ha; subst a; trivial
  · exact checked1266
theorem derived1266 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1266 := by
  apply localUnsat_implies_entails f1266 [c109, c112, c21, c98, c250] c1266 unsat1266 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c250 := h 249 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1267 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1267 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c13, some c355, some c353, some c1265, some c153, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1267 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1267 : lratChecker f1267 p1267 = .success := by decide +kernel
theorem unsat1267 : Unsatisfiable (PosFin 57) f1267 := by
  apply lratCheckerSound f1267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1267
  · intro a ha; simp [p1267] at ha; subst a; trivial
  · exact checked1267
theorem derived1267 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1267 := by
  apply localUnsat_implies_entails f1267 [c13, c355, c353, c1265, c153] c1267 unsat1267 (by rfl) a
  have h0 : Entails.eval a c13 := h 12 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c1265 := derived1265 a h
  have h4 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1268 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨41, by decide⟩, true), (⟨43, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, true), (⟨19, by decide⟩, false), (⟨38, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1268 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c62, some c1236, some c107, some c335, some c61, some c25, some c1237, some c254, some c385, some c96, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨41, by decide⟩, false)), some (DefaultClause.unit (⟨43, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1268 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1268 : lratChecker f1268 p1268 = .success := by decide +kernel
theorem unsat1268 : Unsatisfiable (PosFin 57) f1268 := by
  apply lratCheckerSound f1268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1268
  · intro a ha; simp [p1268] at ha; subst a; trivial
  · exact checked1268
theorem derived1268 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1268 := by
  apply localUnsat_implies_entails f1268 [c62, c1236, c107, c335, c61, c25, c1237, c254, c385, c96] c1268 unsat1268 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c1236 := derived1236 a h
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c335 := h 334 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c1237 := derived1237 a h
  have h7 : Entails.eval a c254 := h 253 (by decide)
  have h8 : Entails.eval a c385 := h 384 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1269 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1269 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c353, some c1264, some c3, some c1074, some c1266, some c1267, some c1, some c113, some c273, some c134, some c326, some c1268, some c356, some c59, some c71, some c385, some c390, some c107, some c1237, some c363, some c1233, some c89, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1269 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked1269 : lratChecker f1269 p1269 = .success := by decide +kernel
theorem unsat1269 : Unsatisfiable (PosFin 57) f1269 := by
  apply lratCheckerSound f1269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1269
  · intro a ha; simp [p1269] at ha; subst a; trivial
  · exact checked1269
theorem derived1269 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1269 := by
  apply localUnsat_implies_entails f1269 [c355, c353, c1264, c3, c1074, c1266, c1267, c1, c113, c273, c134, c326, c1268, c356, c59, c71, c385, c390, c107, c1237, c363, c1233, c89] c1269 unsat1269 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c1264 := derived1264 a h
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c1074 := derived1074 a h
  have h5 : Entails.eval a c1266 := derived1266 a h
  have h6 : Entails.eval a c1267 := derived1267 a h
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c273 := h 272 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c326 := h 325 (by decide)
  have h12 : Entails.eval a c1268 := derived1268 a h
  have h13 : Entails.eval a c356 := h 355 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c71 := h 70 (by decide)
  have h16 : Entails.eval a c385 := h 384 (by decide)
  have h17 : Entails.eval a c390 := h 389 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c1237 := derived1237 a h
  have h20 : Entails.eval a c363 := h 362 (by decide)
  have h21 : Entails.eval a c1233 := derived1233 a h
  have h22 : Entails.eval a c89 := h 88 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1270 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨36, by decide⟩, true), (⟨5, by decide⟩, false), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨55, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1270 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c59, some c23, some c71, some c385, some c251, some c21, some c110, some c1233, some c1231, some c107, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false))]
def p1270 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1270 : lratChecker f1270 p1270 = .success := by decide +kernel
theorem unsat1270 : Unsatisfiable (PosFin 57) f1270 := by
  apply lratCheckerSound f1270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1270
  · intro a ha; simp [p1270] at ha; subst a; trivial
  · exact checked1270
theorem derived1270 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1270 := by
  apply localUnsat_implies_entails f1270 [c59, c23, c71, c385, c251, c21, c110, c1233, c1231, c107] c1270 unsat1270 (by rfl) a
  have h0 : Entails.eval a c59 := h 58 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c385 := h 384 (by decide)
  have h4 : Entails.eval a c251 := h 250 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c1233 := derived1233 a h
  have h8 : Entails.eval a c1231 := derived1231 a h
  have h9 : Entails.eval a c107 := h 106 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1271 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨1, by decide⟩, false), (⟨23, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨36, by decide⟩, true), (⟨9, by decide⟩, true), (⟨35, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1271 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c224, some c266, some c113, some c273, some c41, some c210, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1271 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked1271 : lratChecker f1271 p1271 = .success := by decide +kernel
theorem unsat1271 : Unsatisfiable (PosFin 57) f1271 := by
  apply lratCheckerSound f1271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1271
  · intro a ha; simp [p1271] at ha; subst a; trivial
  · exact checked1271
theorem derived1271 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1271 := by
  apply localUnsat_implies_entails f1271 [c355, c224, c266, c113, c273, c41, c210] c1271 unsat1271 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c224 := h 223 (by decide)
  have h2 : Entails.eval a c266 := h 265 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c273 := h 272 (by decide)
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1272 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨51, by decide⟩, false), (⟨18, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨4, by decide⟩, false), (⟨36, by decide⟩, true), (⟨11, by decide⟩, false), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1272 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c355, some c1271, some c251, some c268, some c263, some c349, some c121, some c113, some c188, some c205, some c41, some c42, some c147, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1272 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked1272 : lratChecker f1272 p1272 = .success := by decide +kernel
theorem unsat1272 : Unsatisfiable (PosFin 57) f1272 := by
  apply lratCheckerSound f1272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1272
  · intro a ha; simp [p1272] at ha; subst a; trivial
  · exact checked1272
theorem derived1272 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1272 := by
  apply localUnsat_implies_entails f1272 [c152, c355, c1271, c251, c268, c263, c349, c121, c113, c188, c205, c41, c42, c147] c1272 unsat1272 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c1271 := derived1271 a h
  have h3 : Entails.eval a c251 := h 250 (by decide)
  have h4 : Entails.eval a c268 := h 267 (by decide)
  have h5 : Entails.eval a c263 := h 262 (by decide)
  have h6 : Entails.eval a c349 := h 348 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  have h9 : Entails.eval a c188 := h 187 (by decide)
  have h10 : Entails.eval a c205 := h 204 (by decide)
  have h11 : Entails.eval a c41 := h 40 (by decide)
  have h12 : Entails.eval a c42 := h 41 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1273 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1273 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1269, some c152, some c355, some c353, some c1264, some c1270, some c109, some c112, some c1266, some c66, some c21, some c98, some c34, some c184, some c12, some c1272, some c1, some c266, some c263, some c224, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1273 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1273 : lratChecker f1273 p1273 = .success := by decide +kernel
theorem unsat1273 : Unsatisfiable (PosFin 57) f1273 := by
  apply lratCheckerSound f1273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1273
  · intro a ha; simp [p1273] at ha; subst a; trivial
  · exact checked1273
theorem derived1273 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1273 := by
  apply localUnsat_implies_entails f1273 [c1269, c152, c355, c353, c1264, c1270, c109, c112, c1266, c66, c21, c98, c34, c184, c12, c1272, c1, c266, c263, c224] c1273 unsat1273 (by rfl) a
  have h0 : Entails.eval a c1269 := derived1269 a h
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c1264 := derived1264 a h
  have h5 : Entails.eval a c1270 := derived1270 a h
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  have h8 : Entails.eval a c1266 := derived1266 a h
  have h9 : Entails.eval a c66 := h 65 (by decide)
  have h10 : Entails.eval a c21 := h 20 (by decide)
  have h11 : Entails.eval a c98 := h 97 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c184 := h 183 (by decide)
  have h14 : Entails.eval a c12 := h 11 (by decide)
  have h15 : Entails.eval a c1272 := derived1272 a h
  have h16 : Entails.eval a c1 := h 0 (by decide)
  have h17 : Entails.eval a c266 := h 265 (by decide)
  have h18 : Entails.eval a c263 := h 262 (by decide)
  have h19 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1274 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨16, by decide⟩, true), (⟨4, by decide⟩, true), (⟨9, by decide⟩, true), (⟨5, by decide⟩, false), (⟨34, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1274 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1, some c10, some c1212, some c110, some c21, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1274 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked1274 : lratChecker f1274 p1274 = .success := by decide +kernel
theorem unsat1274 : Unsatisfiable (PosFin 57) f1274 := by
  apply lratCheckerSound f1274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1274
  · intro a ha; simp [p1274] at ha; subst a; trivial
  · exact checked1274
theorem derived1274 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1274 := by
  apply localUnsat_implies_entails f1274 [c1, c10, c1212, c110, c21] c1274 unsat1274 (by rfl) a
  have h0 : Entails.eval a c1 := h 0 (by decide)
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c1212 := derived1212 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c1275 : DefaultClause 57 := directClause [(⟨5, by decide⟩, false), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1275 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c353, some c1264, some c1269, some c152, some c1273, some c356, some c62, some c1236, some c112, some c161, some c1274, some c107, some c25, some c66, some c110, some c1232, some c17, some c8, some c185, some c270, some c32, some c251, some c1183, some c114, some c113, some c39, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1275 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked1275 : lratChecker f1275 p1275 = .success := by decide +kernel
theorem unsat1275 : Unsatisfiable (PosFin 57) f1275 := by
  apply lratCheckerSound f1275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1275
  · intro a ha; simp [p1275] at ha; subst a; trivial
  · exact checked1275
theorem derived1275 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1275 := by
  apply localUnsat_implies_entails f1275 [c355, c353, c1264, c1269, c152, c1273, c356, c62, c1236, c112, c161, c1274, c107, c25, c66, c110, c1232, c17, c8, c185, c270, c32, c251, c1183, c114, c113, c39] c1275 unsat1275 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c1264 := derived1264 a h
  have h3 : Entails.eval a c1269 := derived1269 a h
  have h4 : Entails.eval a c152 := h 151 (by decide)
  have h5 : Entails.eval a c1273 := derived1273 a h
  have h6 : Entails.eval a c356 := h 355 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c1236 := derived1236 a h
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c161 := h 160 (by decide)
  have h11 : Entails.eval a c1274 := derived1274 a h
  have h12 : Entails.eval a c107 := h 106 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c66 := h 65 (by decide)
  have h15 : Entails.eval a c110 := h 109 (by decide)
  have h16 : Entails.eval a c1232 := derived1232 a h
  have h17 : Entails.eval a c17 := h 16 (by decide)
  have h18 : Entails.eval a c8 := h 7 (by decide)
  have h19 : Entails.eval a c185 := h 184 (by decide)
  have h20 : Entails.eval a c270 := h 269 (by decide)
  have h21 : Entails.eval a c32 := h 31 (by decide)
  have h22 : Entails.eval a c251 := h 250 (by decide)
  have h23 : Entails.eval a c1183 := derived1183 a h
  have h24 : Entails.eval a c114 := h 113 (by decide)
  have h25 : Entails.eval a c113 := h 112 (by decide)
  have h26 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1276 : DefaultClause 57 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨40, by decide⟩, false), (⟨36, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1276 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c266, some c152, some c161, some c113, some c122, some c273, some c274, some c270, some c210, some c33, some c271, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1276 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1276 : lratChecker f1276 p1276 = .success := by decide +kernel
theorem unsat1276 : Unsatisfiable (PosFin 57) f1276 := by
  apply lratCheckerSound f1276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1276
  · intro a ha; simp [p1276] at ha; subst a; trivial
  · exact checked1276
theorem derived1276 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1276 := by
  apply localUnsat_implies_entails f1276 [c266, c152, c161, c113, c122, c273, c274, c270, c210, c33, c271] c1276 unsat1276 (by rfl) a
  have h0 : Entails.eval a c266 := h 265 (by decide)
  have h1 : Entails.eval a c152 := h 151 (by decide)
  have h2 : Entails.eval a c161 := h 160 (by decide)
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c273 := h 272 (by decide)
  have h6 : Entails.eval a c274 := h 273 (by decide)
  have h7 : Entails.eval a c270 := h 269 (by decide)
  have h8 : Entails.eval a c210 := h 209 (by decide)
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1277 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨36, by decide⟩, false), (⟨37, by decide⟩, false), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1277 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c13, some c162, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1277 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1277 : lratChecker f1277 p1277 = .success := by decide +kernel
theorem unsat1277 : Unsatisfiable (PosFin 57) f1277 := by
  apply lratCheckerSound f1277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1277
  · intro a ha; simp [p1277] at ha; subst a; trivial
  · exact checked1277
theorem derived1277 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1277 := by
  apply localUnsat_implies_entails f1277 [c14, c13, c162] c1277 unsat1277 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c13 := h 12 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1278 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1278 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1275, some c355, some c353, some c107, some c25, some c73, some c71, some c356, some c1236, some c1277, some c152, some c161, some c1276, some c220, some c1212, some c113, some c122, some c273, some c43, some c270, some c212, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1278 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked1278 : lratChecker f1278 p1278 = .success := by decide +kernel
theorem unsat1278 : Unsatisfiable (PosFin 57) f1278 := by
  apply lratCheckerSound f1278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1278
  · intro a ha; simp [p1278] at ha; subst a; trivial
  · exact checked1278
theorem derived1278 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1278 := by
  apply localUnsat_implies_entails f1278 [c1275, c355, c353, c107, c25, c73, c71, c356, c1236, c1277, c152, c161, c1276, c220, c1212, c113, c122, c273, c43, c270, c212] c1278 unsat1278 (by rfl) a
  have h0 : Entails.eval a c1275 := derived1275 a h
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c73 := h 72 (by decide)
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c1236 := derived1236 a h
  have h9 : Entails.eval a c1277 := derived1277 a h
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c1276 := derived1276 a h
  have h13 : Entails.eval a c220 := h 219 (by decide)
  have h14 : Entails.eval a c1212 := derived1212 a h
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c122 := h 121 (by decide)
  have h17 : Entails.eval a c273 := h 272 (by decide)
  have h18 : Entails.eval a c43 := h 42 (by decide)
  have h19 : Entails.eval a c270 := h 269 (by decide)
  have h20 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1279 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1279 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1074, some c33, some c32, some c1183, some c356, some c59, some c1006, some c385, some c92, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1279 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked1279 : lratChecker f1279 p1279 = .success := by decide +kernel
theorem unsat1279 : Unsatisfiable (PosFin 57) f1279 := by
  apply lratCheckerSound f1279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1279
  · intro a ha; simp [p1279] at ha; subst a; trivial
  · exact checked1279
theorem derived1279 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1279 := by
  apply localUnsat_implies_entails f1279 [c1074, c33, c32, c1183, c356, c59, c1006, c385, c92] c1279 unsat1279 (by rfl) a
  have h0 : Entails.eval a c1074 := derived1074 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c1183 := derived1183 a h
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c59 := h 58 (by decide)
  have h6 : Entails.eval a c1006 := derived1006 a h
  have h7 : Entails.eval a c385 := h 384 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1280 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨4, by decide⟩, true), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1280 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c355, some c353, some c1279, some c28, some c1, some c152, some c13, some c153, some c59, some c1006, some c385, some c92, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1280 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1280 : lratChecker f1280 p1280 = .success := by decide +kernel
theorem unsat1280 : Unsatisfiable (PosFin 57) f1280 := by
  apply lratCheckerSound f1280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1280
  · intro a ha; simp [p1280] at ha; subst a; trivial
  · exact checked1280
theorem derived1280 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1280 := by
  apply localUnsat_implies_entails f1280 [c355, c353, c1279, c28, c1, c152, c13, c153, c59, c1006, c385, c92] c1280 unsat1280 (by rfl) a
  have h0 : Entails.eval a c355 := h 354 (by decide)
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c1279 := derived1279 a h
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  have h6 : Entails.eval a c13 := h 12 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c1006 := derived1006 a h
  have h10 : Entails.eval a c385 := h 384 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1281 : DefaultClause 57 := directClause [(⟨9, by decide⟩, false), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1281 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c152, some c155, some c15, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1281 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1281 : lratChecker f1281 p1281 = .success := by decide +kernel
theorem unsat1281 : Unsatisfiable (PosFin 57) f1281 := by
  apply lratCheckerSound f1281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1281
  · intro a ha; simp [p1281] at ha; subst a; trivial
  · exact checked1281
theorem derived1281 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1281 := by
  apply localUnsat_implies_entails f1281 [c152, c155, c15] c1281 unsat1281 (by rfl) a
  have h0 : Entails.eval a c152 := h 151 (by decide)
  have h1 : Entails.eval a c155 := h 154 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1282 : DefaultClause 57 := directClause [(⟨11, by decide⟩, true), (⟨37, by decide⟩, false), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨5, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1282 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c14, some c15, some c164, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1282 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1282 : lratChecker f1282 p1282 = .success := by decide +kernel
theorem unsat1282 : Unsatisfiable (PosFin 57) f1282 := by
  apply lratCheckerSound f1282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1282
  · intro a ha; simp [p1282] at ha; subst a; trivial
  · exact checked1282
theorem derived1282 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1282 := by
  apply localUnsat_implies_entails f1282 [c14, c15, c164] c1282 unsat1282 (by rfl) a
  have h0 : Entails.eval a c14 := h 13 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1283 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1283 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1275, some c353, some c1264, some c1280, some c1278, some c62, some c98, some c356, some c59, some c23, some c390, some c251, some c60, some c21, some c1281, some c1282, some c184, some c114, some c306, some c39, some c305, some c132, some c642, some c326, some c293, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1283 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1283 : lratChecker f1283 p1283 = .success := by decide +kernel
theorem unsat1283 : Unsatisfiable (PosFin 57) f1283 := by
  apply lratCheckerSound f1283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1283
  · intro a ha; simp [p1283] at ha; subst a; trivial
  · exact checked1283
theorem derived1283 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1283 := by
  apply localUnsat_implies_entails f1283 [c1275, c353, c1264, c1280, c1278, c62, c98, c356, c59, c23, c390, c251, c60, c21, c1281, c1282, c184, c114, c306, c39, c305, c132, c642, c326, c293] c1283 unsat1283 (by rfl) a
  have h0 : Entails.eval a c1275 := derived1275 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c1264 := derived1264 a h
  have h3 : Entails.eval a c1280 := derived1280 a h
  have h4 : Entails.eval a c1278 := derived1278 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c390 := h 389 (by decide)
  have h11 : Entails.eval a c251 := h 250 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c21 := h 20 (by decide)
  have h14 : Entails.eval a c1281 := derived1281 a h
  have h15 : Entails.eval a c1282 := derived1282 a h
  have h16 : Entails.eval a c184 := h 183 (by decide)
  have h17 : Entails.eval a c114 := h 113 (by decide)
  have h18 : Entails.eval a c306 := h 305 (by decide)
  have h19 : Entails.eval a c39 := h 38 (by decide)
  have h20 : Entails.eval a c305 := h 304 (by decide)
  have h21 : Entails.eval a c132 := h 131 (by decide)
  have h22 : Entails.eval a c642 := derived642 a h
  have h23 : Entails.eval a c326 := h 325 (by decide)
  have h24 : Entails.eval a c293 := h 292 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1284 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨9, by decide⟩, true), (⟨36, by decide⟩, true), (⟨51, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1284 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c353, some c104, some c21, some c250, some c33, some c34, some c1271, some c271, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1284 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked1284 : lratChecker f1284 p1284 = .success := by decide +kernel
theorem unsat1284 : Unsatisfiable (PosFin 57) f1284 := by
  apply lratCheckerSound f1284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1284
  · intro a ha; simp [p1284] at ha; subst a; trivial
  · exact checked1284
theorem derived1284 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1284 := by
  apply localUnsat_implies_entails f1284 [c353, c104, c21, c250, c33, c34, c1271, c271] c1284 unsat1284 (by rfl) a
  have h0 : Entails.eval a c353 := h 352 (by decide)
  have h1 : Entails.eval a c104 := h 103 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c250 := h 249 (by decide)
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c1271 := derived1271 a h
  have h7 : Entails.eval a c271 := h 270 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1285 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1285 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1283, some c1275, some c355, some c353, some c1264, some c62, some c98, some c356, some c1281, some c1284, some c1, some c1074, some c33, some c34, some c1246, some c266, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1285 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1285 : lratChecker f1285 p1285 = .success := by decide +kernel
theorem unsat1285 : Unsatisfiable (PosFin 57) f1285 := by
  apply lratCheckerSound f1285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1285
  · intro a ha; simp [p1285] at ha; subst a; trivial
  · exact checked1285
theorem derived1285 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1285 := by
  apply localUnsat_implies_entails f1285 [c1283, c1275, c355, c353, c1264, c62, c98, c356, c1281, c1284, c1, c1074, c33, c34, c1246, c266] c1285 unsat1285 (by rfl) a
  have h0 : Entails.eval a c1283 := derived1283 a h
  have h1 : Entails.eval a c1275 := derived1275 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c1264 := derived1264 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c356 := h 355 (by decide)
  have h8 : Entails.eval a c1281 := derived1281 a h
  have h9 : Entails.eval a c1284 := derived1284 a h
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c1074 := derived1074 a h
  have h12 : Entails.eval a c33 := h 32 (by decide)
  have h13 : Entails.eval a c34 := h 33 (by decide)
  have h14 : Entails.eval a c1246 := derived1246 a h
  have h15 : Entails.eval a c266 := h 265 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1286 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨23, by decide⟩, true), (⟨21, by decide⟩, false), (⟨11, by decide⟩, false), (⟨13, by decide⟩, false), (⟨36, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1286 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c384, some c184, some c428, some c1231, some c390, some c252, some c1235, some c21, some c114, some c124, some c161, some c47, some c45, some c205, some c148, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p1286 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked1286 : lratChecker f1286 p1286 = .success := by decide +kernel
theorem unsat1286 : Unsatisfiable (PosFin 57) f1286 := by
  apply lratCheckerSound f1286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1286
  · intro a ha; simp [p1286] at ha; subst a; trivial
  · exact checked1286
theorem derived1286 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1286 := by
  apply localUnsat_implies_entails f1286 [c106, c384, c184, c428, c1231, c390, c252, c1235, c21, c114, c124, c161, c47, c45, c205, c148] c1286 unsat1286 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c384 := h 383 (by decide)
  have h2 : Entails.eval a c184 := h 183 (by decide)
  have h3 : Entails.eval a c428 := derived428 a h
  have h4 : Entails.eval a c1231 := derived1231 a h
  have h5 : Entails.eval a c390 := h 389 (by decide)
  have h6 : Entails.eval a c252 := h 251 (by decide)
  have h7 : Entails.eval a c1235 := derived1235 a h
  have h8 : Entails.eval a c21 := h 20 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c47 := h 46 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c205 := h 204 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1287 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨36, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨38, by decide⟩, true), (⟨34, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1287 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c1, some c9, some c1074, some c3, some c33, some c1246, some c266, some c1286, some c97, some c186, some c390, some c252, some c349, some c1235, some c21, some c114, some c124, some c248, some c161, some c45, some c205, some c1231, some c148, some c47, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1287 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked1287 : lratChecker f1287 p1287 = .success := by decide +kernel
theorem unsat1287 : Unsatisfiable (PosFin 57) f1287 := by
  apply lratCheckerSound f1287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1287
  · intro a ha; simp [p1287] at ha; subst a; trivial
  · exact checked1287
theorem derived1287 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1287 := by
  apply localUnsat_implies_entails f1287 [c106, c1, c9, c1074, c3, c33, c1246, c266, c1286, c97, c186, c390, c252, c349, c1235, c21, c114, c124, c248, c161, c45, c205, c1231, c148, c47] c1287 unsat1287 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c1 := h 0 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c1074 := derived1074 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c1246 := derived1246 a h
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c1286 := derived1286 a h
  have h9 : Entails.eval a c97 := h 96 (by decide)
  have h10 : Entails.eval a c186 := h 185 (by decide)
  have h11 : Entails.eval a c390 := h 389 (by decide)
  have h12 : Entails.eval a c252 := h 251 (by decide)
  have h13 : Entails.eval a c349 := h 348 (by decide)
  have h14 : Entails.eval a c1235 := derived1235 a h
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c124 := h 123 (by decide)
  have h18 : Entails.eval a c248 := h 247 (by decide)
  have h19 : Entails.eval a c161 := h 160 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c205 := h 204 (by decide)
  have h22 : Entails.eval a c1231 := derived1231 a h
  have h23 : Entails.eval a c148 := h 147 (by decide)
  have h24 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1288 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨21, by decide⟩, false), (⟨17, by decide⟩, true), (⟨39, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1288 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c356, some c355, some c353, some c390, some c252, some c349, some c21, some c1250, some c1256, some c73, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1288 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked1288 : lratChecker f1288 p1288 = .success := by decide +kernel
theorem unsat1288 : Unsatisfiable (PosFin 57) f1288 := by
  apply lratCheckerSound f1288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1288
  · intro a ha; simp [p1288] at ha; subst a; trivial
  · exact checked1288
theorem derived1288 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1288 := by
  apply localUnsat_implies_entails f1288 [c356, c355, c353, c390, c252, c349, c21, c1250, c1256, c73] c1288 unsat1288 (by rfl) a
  have h0 : Entails.eval a c356 := h 355 (by decide)
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c390 := h 389 (by decide)
  have h4 : Entails.eval a c252 := h 251 (by decide)
  have h5 : Entails.eval a c349 := h 348 (by decide)
  have h6 : Entails.eval a c21 := h 20 (by decide)
  have h7 : Entails.eval a c1250 := derived1250 a h
  have h8 : Entails.eval a c1256 := derived1256 a h
  have h9 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1289 : DefaultClause 57 := directClause [(⟨53, by decide⟩, true), (⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f1289 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c97, some c92, some c384, some (DefaultClause.unit (⟨53, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p1289 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked1289 : lratChecker f1289 p1289 = .success := by decide +kernel
theorem unsat1289 : Unsatisfiable (PosFin 57) f1289 := by
  apply lratCheckerSound f1289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1289
  · intro a ha; simp [p1289] at ha; subst a; trivial
  · exact checked1289
theorem derived1289 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1289 := by
  apply localUnsat_implies_entails f1289 [c97, c92, c384] c1289 unsat1289 (by rfl) a
  have h0 : Entails.eval a c97 := h 96 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c384 := h 383 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c1290 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1290 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c106, some c1289, some c355, some c353, some c356, some c1287, some c152, some c3, some c1074, some c28, some c1288, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1290 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked1290 : lratChecker f1290 p1290 = .success := by decide +kernel
theorem unsat1290 : Unsatisfiable (PosFin 57) f1290 := by
  apply lratCheckerSound f1290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1290
  · intro a ha; simp [p1290] at ha; subst a; trivial
  · exact checked1290
theorem derived1290 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1290 := by
  apply localUnsat_implies_entails f1290 [c106, c1289, c355, c353, c356, c1287, c152, c3, c1074, c28, c1288] c1290 unsat1290 (by rfl) a
  have h0 : Entails.eval a c106 := h 105 (by decide)
  have h1 : Entails.eval a c1289 := derived1289 a h
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c353 := h 352 (by decide)
  have h4 : Entails.eval a c356 := h 355 (by decide)
  have h5 : Entails.eval a c1287 := derived1287 a h
  have h6 : Entails.eval a c152 := h 151 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c1074 := derived1074 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c1288 := derived1288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1291 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨39, by decide⟩, true), (⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨5, by decide⟩, true), (⟨35, by decide⟩, false), (⟨50, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1291 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1289, some c355, some c353, some c252, some c21, some c219, some c220, some c266, some c271, some c1, some c152, some c3, some c14, some c270, some c186, some c29, some c114, some c45, some c47, some c214, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1291 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked1291 : lratChecker f1291 p1291 = .success := by decide +kernel
theorem unsat1291 : Unsatisfiable (PosFin 57) f1291 := by
  apply lratCheckerSound f1291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1291
  · intro a ha; simp [p1291] at ha; subst a; trivial
  · exact checked1291
theorem derived1291 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1291 := by
  apply localUnsat_implies_entails f1291 [c1289, c355, c353, c252, c21, c219, c220, c266, c271, c1, c152, c3, c14, c270, c186, c29, c114, c45, c47, c214] c1291 unsat1291 (by rfl) a
  have h0 : Entails.eval a c1289 := derived1289 a h
  have h1 : Entails.eval a c355 := h 354 (by decide)
  have h2 : Entails.eval a c353 := h 352 (by decide)
  have h3 : Entails.eval a c252 := h 251 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c219 := h 218 (by decide)
  have h6 : Entails.eval a c220 := h 219 (by decide)
  have h7 : Entails.eval a c266 := h 265 (by decide)
  have h8 : Entails.eval a c271 := h 270 (by decide)
  have h9 : Entails.eval a c1 := h 0 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c14 := h 13 (by decide)
  have h13 : Entails.eval a c270 := h 269 (by decide)
  have h14 : Entails.eval a c186 := h 185 (by decide)
  have h15 : Entails.eval a c29 := h 28 (by decide)
  have h16 : Entails.eval a c114 := h 113 (by decide)
  have h17 : Entails.eval a c45 := h 44 (by decide)
  have h18 : Entails.eval a c47 := h 46 (by decide)
  have h19 : Entails.eval a c214 := h 213 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1292 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨55, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1292 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c1264, some c353, some c355, some c1275, some c1283, some c1285, some c106, some c1290, some c1291, some c33, some c28, some c1074, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1292 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked1292 : lratChecker f1292 p1292 = .success := by decide +kernel
theorem unsat1292 : Unsatisfiable (PosFin 57) f1292 := by
  apply lratCheckerSound f1292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1292
  · intro a ha; simp [p1292] at ha; subst a; trivial
  · exact checked1292
theorem derived1292 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1292 := by
  apply localUnsat_implies_entails f1292 [c1264, c353, c355, c1275, c1283, c1285, c106, c1290, c1291, c33, c28, c1074] c1292 unsat1292 (by rfl) a
  have h0 : Entails.eval a c1264 := derived1264 a h
  have h1 : Entails.eval a c353 := h 352 (by decide)
  have h2 : Entails.eval a c355 := h 354 (by decide)
  have h3 : Entails.eval a c1275 := derived1275 a h
  have h4 : Entails.eval a c1283 := derived1283 a h
  have h5 : Entails.eval a c1285 := derived1285 a h
  have h6 : Entails.eval a c106 := h 105 (by decide)
  have h7 : Entails.eval a c1290 := derived1290 a h
  have h8 : Entails.eval a c1291 := derived1291 a h
  have h9 : Entails.eval a c33 := h 32 (by decide)
  have h10 : Entails.eval a c28 := h 27 (by decide)
  have h11 : Entails.eval a c1074 := derived1074 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c1293 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨37, by decide⟩, false), (⟨53, by decide⟩, false), (⟨5, by decide⟩, true), (⟨40, by decide⟩, false), (⟨8, by decide⟩, false), (⟨1, by decide⟩, true), (⟨4, by decide⟩, false), (⟨18, by decide⟩, true), (⟨19, by decide⟩, false), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f1293 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c360, some c21, some c5, some c28, some c186, some c165, some c1074, some c1174, some c114, some c154, some c45, some c47, some c657, some c141, some c275, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p1293 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked1293 : lratChecker f1293 p1293 = .success := by decide +kernel
theorem unsat1293 : Unsatisfiable (PosFin 57) f1293 := by
  apply lratCheckerSound f1293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p1293
  · intro a ha; simp [p1293] at ha; subst a; trivial
  · exact checked1293
theorem derived1293 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c1293 := by
  apply localUnsat_implies_entails f1293 [c360, c21, c5, c28, c186, c165, c1074, c1174, c114, c154, c45, c47, c657, c141, c275] c1293 unsat1293 (by rfl) a
  have h0 : Entails.eval a c360 := h 359 (by decide)
  have h1 : Entails.eval a c21 := h 20 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c28 := h 27 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c1074 := derived1074 a h
  have h7 : Entails.eval a c1174 := derived1174 a h
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c657 := derived657 a h
  have h13 : Entails.eval a c141 := h 140 (by decide)
  have h14 : Entails.eval a c275 := h 274 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived1293

end CochromaticTwenty.Certificates.B16_0_0
