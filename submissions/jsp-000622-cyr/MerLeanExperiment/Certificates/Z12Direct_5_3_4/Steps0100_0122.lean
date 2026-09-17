import MerLeanExperiment.Certificates.Z12Direct_5_3_4.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_3_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c311 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f311 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c306, some c274, some c310, some c52, some c44, some c49, some c145, some c127, some c94, some c103, some c138, some c4, some c79, some c113, some c202, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p311 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked311 : lratChecker f311 p311 = .success := by decide +kernel
theorem unsat311 : Unsatisfiable (PosFin 31) f311 := by
  apply lratCheckerSound f311 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p311
  · intro a ha; simp [p311] at ha; subst a; trivial
  · exact checked311
theorem derived311 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c311 := by
  apply localUnsat_implies_entails f311 [c252, c303, c306, c274, c310, c52, c44, c49, c145, c127, c94, c103, c138, c4, c79, c113, c202] c311 unsat311 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c310 := derived310 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c44 := h 43 (by decide)
  have h7 : Entails.eval a c49 := h 48 (by decide)
  have h8 : Entails.eval a c145 := h 144 (by decide)
  have h9 : Entails.eval a c127 := h 126 (by decide)
  have h10 : Entails.eval a c94 := h 93 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c138 := h 137 (by decide)
  have h13 : Entails.eval a c4 := h 3 (by decide)
  have h14 : Entails.eval a c79 := h 78 (by decide)
  have h15 : Entails.eval a c113 := h 112 (by decide)
  have h16 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c312 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f312 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c311, some c306, some c274, some c310, some c52, some c44, some c49, some c145, some c307, some c304, some c132, some c117, some c174, some c210, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p312 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked312 : lratChecker f312 p312 = .success := by decide +kernel
theorem unsat312 : Unsatisfiable (PosFin 31) f312 := by
  apply lratCheckerSound f312 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p312
  · intro a ha; simp [p312] at ha; subst a; trivial
  · exact checked312
theorem derived312 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c312 := by
  apply localUnsat_implies_entails f312 [c252, c303, c311, c306, c274, c310, c52, c44, c49, c145, c307, c304, c132, c117, c174, c210] c312 unsat312 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c311 := derived311 a h
  have h3 : Entails.eval a c306 := derived306 a h
  have h4 : Entails.eval a c274 := derived274 a h
  have h5 : Entails.eval a c310 := derived310 a h
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c44 := h 43 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c307 := derived307 a h
  have h11 : Entails.eval a c304 := derived304 a h
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c117 := h 116 (by decide)
  have h14 : Entails.eval a c174 := h 173 (by decide)
  have h15 : Entails.eval a c210 := h 209 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c313 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f313 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c306, some c274, some c310, some c52, some c311, some c312, some c27, some c135, some c177, some c3, some c81, some c37, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p313 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked313 : lratChecker f313 p313 = .success := by decide +kernel
theorem unsat313 : Unsatisfiable (PosFin 31) f313 := by
  apply lratCheckerSound f313 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p313
  · intro a ha; simp [p313] at ha; subst a; trivial
  · exact checked313
theorem derived313 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c313 := by
  apply localUnsat_implies_entails f313 [c252, c303, c306, c274, c310, c52, c311, c312, c27, c135, c177, c3, c81, c37] c313 unsat313 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c310 := derived310 a h
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c311 := derived311 a h
  have h7 : Entails.eval a c312 := derived312 a h
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c135 := h 134 (by decide)
  have h10 : Entails.eval a c177 := h 176 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c314 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f314 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c303, some c306, some c313, some c123, some c27, some c90, some c37, some c4, some c140, some c94, some c127, some c134, some c89, some c79, some c122, some c163, some c146, some c160, some c147, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p314 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked314 : lratChecker f314 p314 = .success := by decide +kernel
theorem unsat314 : Unsatisfiable (PosFin 31) f314 := by
  apply lratCheckerSound f314 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p314
  · intro a ha; simp [p314] at ha; subst a; trivial
  · exact checked314
theorem derived314 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c314 := by
  apply localUnsat_implies_entails f314 [c303, c306, c313, c123, c27, c90, c37, c4, c140, c94, c127, c134, c89, c79, c122, c163, c146, c160, c147] c314 unsat314 (by rfl) a
  have h0 : Entails.eval a c303 := derived303 a h
  have h1 : Entails.eval a c306 := derived306 a h
  have h2 : Entails.eval a c313 := derived313 a h
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c90 := h 89 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c140 := h 139 (by decide)
  have h9 : Entails.eval a c94 := h 93 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c134 := h 133 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c79 := h 78 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  have h16 : Entails.eval a c146 := h 145 (by decide)
  have h17 : Entails.eval a c160 := h 159 (by decide)
  have h18 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c315 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f315 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c303, some c306, some c313, some c90, some c123, some c37, some c27, some c4, some c140, some c127, some c94, some c134, some c89, some c122, some c79, some c314, some c116, some c121, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p315 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked315 : lratChecker f315 p315 = .success := by decide +kernel
theorem unsat315 : Unsatisfiable (PosFin 31) f315 := by
  apply lratCheckerSound f315 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p315
  · intro a ha; simp [p315] at ha; subst a; trivial
  · exact checked315
theorem derived315 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c315 := by
  apply localUnsat_implies_entails f315 [c252, c303, c306, c313, c90, c123, c37, c27, c4, c140, c127, c94, c134, c89, c122, c79, c314, c116, c121] c315 unsat315 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c303 := derived303 a h
  have h2 : Entails.eval a c306 := derived306 a h
  have h3 : Entails.eval a c313 := derived313 a h
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c127 := h 126 (by decide)
  have h11 : Entails.eval a c94 := h 93 (by decide)
  have h12 : Entails.eval a c134 := h 133 (by decide)
  have h13 : Entails.eval a c89 := h 88 (by decide)
  have h14 : Entails.eval a c122 := h 121 (by decide)
  have h15 : Entails.eval a c79 := h 78 (by decide)
  have h16 : Entails.eval a c314 := derived314 a h
  have h17 : Entails.eval a c116 := h 115 (by decide)
  have h18 : Entails.eval a c121 := h 120 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c316 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f316 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c205, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p316 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked316 : lratChecker f316 p316 = .success := by decide +kernel
theorem unsat316 : Unsatisfiable (PosFin 31) f316 := by
  apply lratCheckerSound f316 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p316
  · intro a ha; simp [p316] at ha; subst a; trivial
  · exact checked316
theorem derived316 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c316 := by
  apply localUnsat_implies_entails f316 [c315, c205] c316 unsat316 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c205 := h 204 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c317 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f317 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c252, some c142, some c49, some c47, some c152, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p317 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked317 : lratChecker f317 p317 = .success := by decide +kernel
theorem unsat317 : Unsatisfiable (PosFin 31) f317 := by
  apply lratCheckerSound f317 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p317
  · intro a ha; simp [p317] at ha; subst a; trivial
  · exact checked317
theorem derived317 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c317 := by
  apply localUnsat_implies_entails f317 [c315, c252, c142, c49, c47, c152] c317 unsat317 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c49 := h 48 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c318 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f318 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c252, some c316, some c303, some c142, some c317, some c144, some c208, some c168, some c187, some c152, some c3, some c31, some c25, some c198, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p318 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked318 : lratChecker f318 p318 = .success := by decide +kernel
theorem unsat318 : Unsatisfiable (PosFin 31) f318 := by
  apply lratCheckerSound f318 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p318
  · intro a ha; simp [p318] at ha; subst a; trivial
  · exact checked318
theorem derived318 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c318 := by
  apply localUnsat_implies_entails f318 [c315, c252, c316, c303, c142, c317, c144, c208, c168, c187, c152, c3, c31, c25, c198] c318 unsat318 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c316 := derived316 a h
  have h3 : Entails.eval a c303 := derived303 a h
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c317 := derived317 a h
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c31 := h 30 (by decide)
  have h13 : Entails.eval a c25 := h 24 (by decide)
  have h14 : Entails.eval a c198 := h 197 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c319 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f319 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c252, some c303, some c316, some c142, some c317, some c144, some c208, some c168, some c187, some c152, some c318, some c40, some c35, some c195, some c31, some c25, some c21, some (DefaultClause.unit (⟨27, by decide⟩, false))]
def p319 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked319 : lratChecker f319 p319 = .success := by decide +kernel
theorem unsat319 : Unsatisfiable (PosFin 31) f319 := by
  apply lratCheckerSound f319 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p319
  · intro a ha; simp [p319] at ha; subst a; trivial
  · exact checked319
theorem derived319 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c319 := by
  apply localUnsat_implies_entails f319 [c315, c252, c303, c316, c142, c317, c144, c208, c168, c187, c152, c318, c40, c35, c195, c31, c25, c21] c319 unsat319 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c303 := derived303 a h
  have h3 : Entails.eval a c316 := derived316 a h
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c317 := derived317 a h
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c208 := h 207 (by decide)
  have h8 : Entails.eval a c168 := h 167 (by decide)
  have h9 : Entails.eval a c187 := h 186 (by decide)
  have h10 : Entails.eval a c152 := h 151 (by decide)
  have h11 : Entails.eval a c318 := derived318 a h
  have h12 : Entails.eval a c40 := h 39 (by decide)
  have h13 : Entails.eval a c35 := h 34 (by decide)
  have h14 : Entails.eval a c195 := h 194 (by decide)
  have h15 : Entails.eval a c31 := h 30 (by decide)
  have h16 : Entails.eval a c25 := h 24 (by decide)
  have h17 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c320 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f320 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c319, some c315, some c252, some c316, some c49, some c190, some c144, some c168, some c52, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p320 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked320 : lratChecker f320 p320 = .success := by decide +kernel
theorem unsat320 : Unsatisfiable (PosFin 31) f320 := by
  apply lratCheckerSound f320 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p320
  · intro a ha; simp [p320] at ha; subst a; trivial
  · exact checked320
theorem derived320 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c320 := by
  apply localUnsat_implies_entails f320 [c319, c315, c252, c316, c49, c190, c144, c168, c52] c320 unsat320 (by rfl) a
  have h0 : Entails.eval a c319 := derived319 a h
  have h1 : Entails.eval a c315 := derived315 a h
  have h2 : Entails.eval a c252 := derived252 a h
  have h3 : Entails.eval a c316 := derived316 a h
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c168 := h 167 (by decide)
  have h8 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c321 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨19, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f321 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c252, some c316, some c319, some c320, some c207, some c191, some c52, some c144, some c40, some c212, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p321 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked321 : lratChecker f321 p321 = .success := by decide +kernel
theorem unsat321 : Unsatisfiable (PosFin 31) f321 := by
  apply lratCheckerSound f321 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p321
  · intro a ha; simp [p321] at ha; subst a; trivial
  · exact checked321
theorem derived321 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c321 := by
  apply localUnsat_implies_entails f321 [c315, c252, c316, c319, c320, c207, c191, c52, c144, c40, c212] c321 unsat321 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c316 := derived316 a h
  have h3 : Entails.eval a c319 := derived319 a h
  have h4 : Entails.eval a c320 := derived320 a h
  have h5 : Entails.eval a c207 := h 206 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c144 := h 143 (by decide)
  have h9 : Entails.eval a c40 := h 39 (by decide)
  have h10 : Entails.eval a c212 := derived212 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c322 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f322 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c319, some c252, some c315, some c316, some c303, some c320, some c207, some c191, some c153, some c52, some c144, some c321, some c3, some c31, some c26, some c172, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p322 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked322 : lratChecker f322 p322 = .success := by decide +kernel
theorem unsat322 : Unsatisfiable (PosFin 31) f322 := by
  apply lratCheckerSound f322 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p322
  · intro a ha; simp [p322] at ha; subst a; trivial
  · exact checked322
theorem derived322 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c322 := by
  apply localUnsat_implies_entails f322 [c319, c252, c315, c316, c303, c320, c207, c191, c153, c52, c144, c321, c3, c31, c26, c172] c322 unsat322 (by rfl) a
  have h0 : Entails.eval a c319 := derived319 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c315 := derived315 a h
  have h3 : Entails.eval a c316 := derived316 a h
  have h4 : Entails.eval a c303 := derived303 a h
  have h5 : Entails.eval a c320 := derived320 a h
  have h6 : Entails.eval a c207 := h 206 (by decide)
  have h7 : Entails.eval a c191 := h 190 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  have h11 : Entails.eval a c321 := derived321 a h
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c31 := h 30 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c323 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f323 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c319, some c252, some c322, some c153, some c52, some c181, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p323 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked323 : lratChecker f323 p323 = .success := by decide +kernel
theorem unsat323 : Unsatisfiable (PosFin 31) f323 := by
  apply lratCheckerSound f323 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p323
  · intro a ha; simp [p323] at ha; subst a; trivial
  · exact checked323
theorem derived323 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c323 := by
  apply localUnsat_implies_entails f323 [c319, c252, c322, c153, c52, c181] c323 unsat323 (by rfl) a
  have h0 : Entails.eval a c319 := derived319 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c322 := derived322 a h
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c324 : DefaultClause 31 := directClause [(⟨19, by decide⟩, true), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f324 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c319, some c323, some c322, some c181, some c43, some c50, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p324 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked324 : lratChecker f324 p324 = .success := by decide +kernel
theorem unsat324 : Unsatisfiable (PosFin 31) f324 := by
  apply lratCheckerSound f324 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p324
  · intro a ha; simp [p324] at ha; subst a; trivial
  · exact checked324
theorem derived324 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c324 := by
  apply localUnsat_implies_entails f324 [c252, c319, c323, c322, c181, c43, c50] c324 unsat324 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c319 := derived319 a h
  have h2 : Entails.eval a c323 := derived323 a h
  have h3 : Entails.eval a c322 := derived322 a h
  have h4 : Entails.eval a c181 := h 180 (by decide)
  have h5 : Entails.eval a c43 := h 42 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c325 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false), (⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f325 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c315, some c319, some c252, some c180, some c207, some c191, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p325 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked325 : lratChecker f325 p325 = .success := by decide +kernel
theorem unsat325 : Unsatisfiable (PosFin 31) f325 := by
  apply lratCheckerSound f325 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p325
  · intro a ha; simp [p325] at ha; subst a; trivial
  · exact checked325
theorem derived325 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c325 := by
  apply localUnsat_implies_entails f325 [c315, c319, c252, c180, c207, c191] c325 unsat325 (by rfl) a
  have h0 : Entails.eval a c315 := derived315 a h
  have h1 : Entails.eval a c319 := derived319 a h
  have h2 : Entails.eval a c252 := derived252 a h
  have h3 : Entails.eval a c180 := h 179 (by decide)
  have h4 : Entails.eval a c207 := h 206 (by decide)
  have h5 : Entails.eval a c191 := h 190 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c326 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f326 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c323, some c324, some c325, some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p326 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked326 : lratChecker f326 p326 = .success := by decide +kernel
theorem unsat326 : Unsatisfiable (PosFin 31) f326 := by
  apply lratCheckerSound f326 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p326
  · intro a ha; simp [p326] at ha; subst a; trivial
  · exact checked326
theorem derived326 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c326 := by
  apply localUnsat_implies_entails f326 [c323, c324, c325] c326 unsat326 (by rfl) a
  have h0 : Entails.eval a c323 := derived323 a h
  have h1 : Entails.eval a c324 := derived324 a h
  have h2 : Entails.eval a c325 := derived325 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c327 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f327 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c326, some c46, some c274, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p327 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked327 : lratChecker f327 p327 = .success := by decide +kernel
theorem unsat327 : Unsatisfiable (PosFin 31) f327 := by
  apply lratCheckerSound f327 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p327
  · intro a ha; simp [p327] at ha; subst a; trivial
  · exact checked327
theorem derived327 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c327 := by
  apply localUnsat_implies_entails f327 [c252, c326, c46, c274] c327 unsat327 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c326 := derived326 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c274 := derived274 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c328 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f328 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c327, some c319, some c52, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p328 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked328 : lratChecker f328 p328 = .success := by decide +kernel
theorem unsat328 : Unsatisfiable (PosFin 31) f328 := by
  apply lratCheckerSound f328 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p328
  · intro a ha; simp [p328] at ha; subst a; trivial
  · exact checked328
theorem derived328 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c328 := by
  apply localUnsat_implies_entails f328 [c327, c319, c52] c328 unsat328 (by rfl) a
  have h0 : Entails.eval a c327 := derived327 a h
  have h1 : Entails.eval a c319 := derived319 a h
  have h2 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c329 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f329 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c315, some c252, some c144, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p329 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked329 : lratChecker f329 p329 = .success := by decide +kernel
theorem unsat329 : Unsatisfiable (PosFin 31) f329 := by
  apply lratCheckerSound f329 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p329
  · intro a ha; simp [p329] at ha; subst a; trivial
  · exact checked329
theorem derived329 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c329 := by
  apply localUnsat_implies_entails f329 [c328, c315, c252, c144] c329 unsat329 (by rfl) a
  have h0 : Entails.eval a c328 := derived328 a h
  have h1 : Entails.eval a c315 := derived315 a h
  have h2 : Entails.eval a c252 := derived252 a h
  have h3 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c330 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f330 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c328, some c326, some c252, some c44, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p330 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked330 : lratChecker f330 p330 = .success := by decide +kernel
theorem unsat330 : Unsatisfiable (PosFin 31) f330 := by
  apply lratCheckerSound f330 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p330
  · intro a ha; simp [p330] at ha; subst a; trivial
  · exact checked330
theorem derived330 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c330 := by
  apply localUnsat_implies_entails f330 [c328, c326, c252, c44] c330 unsat330 (by rfl) a
  have h0 : Entails.eval a c328 := derived328 a h
  have h1 : Entails.eval a c326 := derived326 a h
  have h2 : Entails.eval a c252 := derived252 a h
  have h3 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c331 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f331 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c329, some c327, some c316, some c164, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p331 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked331 : lratChecker f331 p331 = .success := by decide +kernel
theorem unsat331 : Unsatisfiable (PosFin 31) f331 := by
  apply lratCheckerSound f331 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p331
  · intro a ha; simp [p331] at ha; subst a; trivial
  · exact checked331
theorem derived331 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c331 := by
  apply localUnsat_implies_entails f331 [c329, c327, c316, c164] c331 unsat331 (by rfl) a
  have h0 : Entails.eval a c329 := derived329 a h
  have h1 : Entails.eval a c327 := derived327 a h
  have h2 : Entails.eval a c316 := derived316 a h
  have h3 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c332 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f332 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c330, some c320, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p332 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked332 : lratChecker f332 p332 = .success := by decide +kernel
theorem unsat332 : Unsatisfiable (PosFin 31) f332 := by
  apply lratCheckerSound f332 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p332
  · intro a ha; simp [p332] at ha; subst a; trivial
  · exact checked332
theorem derived332 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c332 := by
  apply localUnsat_implies_entails f332 [c330, c320] c332 unsat332 (by rfl) a
  have h0 : Entails.eval a c330 := derived330 a h
  have h1 : Entails.eval a c320 := derived320 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c333 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f333 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c331, some c332, some c326, some c263]
def p333 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked333 : lratChecker f333 p333 = .success := by decide +kernel
theorem unsat333 : Unsatisfiable (PosFin 31) f333 := by
  apply lratCheckerSound f333 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p333
  · intro a ha; simp [p333] at ha; subst a; trivial
  · exact checked333
theorem derived333 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c333 := by
  apply localUnsat_implies_entails f333 [c331, c332, c326, c263] c333 unsat333 (by rfl) a
  have h0 : Entails.eval a c331 := derived331 a h
  have h1 : Entails.eval a c332 := derived332 a h
  have h2 : Entails.eval a c326 := derived326 a h
  have h3 : Entails.eval a c263 := derived263 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived333

end CochromaticTwenty.Certificates.Z12Direct_5_3_4
