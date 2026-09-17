import MerLeanExperiment.Certificates.Z12Direct_4_0_7.Inputs

/-! Generated from the actual pinned z12direct_4_0_7-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_4_0_7
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c145 : DefaultClause 29 := directClause [(⟨12, by decide⟩, false), (⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f145 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c31, some c34, some c22, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p145 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked145 : lratChecker f145 p145 = .success := by decide +kernel
theorem unsat145 : Unsatisfiable (PosFin 29) f145 := by
  apply lratCheckerSound f145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p145
  · intro a ha; simp [p145] at ha; subst a; trivial
  · exact checked145
theorem derived145 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c145 := by
  apply localUnsat_implies_entails f145 [c31, c34, c22] c145 unsat145 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c146 : DefaultClause 29 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, false), (⟨17, by decide⟩, true), (⟨20, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f146 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c71, some c27, some c8, some c85, some c69, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p146 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked146 : lratChecker f146 p146 = .success := by decide +kernel
theorem unsat146 : Unsatisfiable (PosFin 29) f146 := by
  apply lratCheckerSound f146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p146
  · intro a ha; simp [p146] at ha; subst a; trivial
  · exact checked146
theorem derived146 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c146 := by
  apply localUnsat_implies_entails f146 [c71, c27, c8, c85, c69] c146 unsat146 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c147 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false), (⟨6, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f147 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c30, some c47, some c1, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p147 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked147 : lratChecker f147 p147 = .success := by decide +kernel
theorem unsat147 : Unsatisfiable (PosFin 29) f147 := by
  apply lratCheckerSound f147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p147
  · intro a ha; simp [p147] at ha; subst a; trivial
  · exact checked147
theorem derived147 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c147 := by
  apply localUnsat_implies_entails f147 [c30, c47, c1] c147 unsat147 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c47 := h 46 (by decide)
  have h2 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c148 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f148 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c37, some c108, some c62, some c107, some c61, some c146, some c145, some c41, some c147, some c138, some c129, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p148 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked148 : lratChecker f148 p148 = .success := by decide +kernel
theorem unsat148 : Unsatisfiable (PosFin 29) f148 := by
  apply lratCheckerSound f148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p148
  · intro a ha; simp [p148] at ha; subst a; trivial
  · exact checked148
theorem derived148 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c148 := by
  apply localUnsat_implies_entails f148 [c37, c108, c62, c107, c61, c146, c145, c41, c147, c138, c129] c148 unsat148 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c108 := h 107 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c146 := derived146 a h
  have h6 : Entails.eval a c145 := derived145 a h
  have h7 : Entails.eval a c41 := h 40 (by decide)
  have h8 : Entails.eval a c147 := derived147 a h
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c149 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨14, by decide⟩, true), (⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f149 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c41, some c101, some c48, some c105, some c46, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p149 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked149 : lratChecker f149 p149 = .success := by decide +kernel
theorem unsat149 : Unsatisfiable (PosFin 29) f149 := by
  apply lratCheckerSound f149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p149
  · intro a ha; simp [p149] at ha; subst a; trivial
  · exact checked149
theorem derived149 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c149 := by
  apply localUnsat_implies_entails f149 [c41, c101, c48, c105, c46] c149 unsat149 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c48 := h 47 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c150 : DefaultClause 29 := directClause [(⟨20, by decide⟩, false), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f150 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c108, some c71, some c37, some c72, some c148, some c42, some c149, some c145, some c136, some c119, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p150 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked150 : lratChecker f150 p150 = .success := by decide +kernel
theorem unsat150 : Unsatisfiable (PosFin 29) f150 := by
  apply lratCheckerSound f150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p150
  · intro a ha; simp [p150] at ha; subst a; trivial
  · exact checked150
theorem derived150 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c150 := by
  apply localUnsat_implies_entails f150 [c108, c71, c37, c72, c148, c42, c149, c145, c136, c119] c150 unsat150 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c72 := h 71 (by decide)
  have h4 : Entails.eval a c148 := derived148 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c149 := derived149 a h
  have h7 : Entails.eval a c145 := derived145 a h
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c151 : DefaultClause 29 := directClause [(⟨1, by decide⟩, false), (⟨14, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨16, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f151 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c42, some c51, some c96, some c74, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p151 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked151 : lratChecker f151 p151 = .success := by decide +kernel
theorem unsat151 : Unsatisfiable (PosFin 29) f151 := by
  apply lratCheckerSound f151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p151
  · intro a ha; simp [p151] at ha; subst a; trivial
  · exact checked151
theorem derived151 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c151 := by
  apply localUnsat_implies_entails f151 [c42, c51, c96, c74] c151 unsat151 (by rfl) a
  have h0 : Entails.eval a c42 := h 41 (by decide)
  have h1 : Entails.eval a c51 := h 50 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c152 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f152 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c151, some c103, some c99, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p152 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked152 : lratChecker f152 p152 = .success := by decide +kernel
theorem unsat152 : Unsatisfiable (PosFin 29) f152 := by
  apply lratCheckerSound f152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p152
  · intro a ha; simp [p152] at ha; subst a; trivial
  · exact checked152
theorem derived152 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c152 := by
  apply localUnsat_implies_entails f152 [c107, c61, c151, c103, c99] c152 unsat152 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c151 := derived151 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c153 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true), (⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f153 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c38, some c135, some c30, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p153 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked153 : lratChecker f153 p153 = .success := by decide +kernel
theorem unsat153 : Unsatisfiable (PosFin 29) f153 := by
  apply lratCheckerSound f153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p153
  · intro a ha; simp [p153] at ha; subst a; trivial
  · exact checked153
theorem derived153 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c153 := by
  apply localUnsat_implies_entails f153 [c38, c135, c30] c153 unsat153 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c154 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false), (⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f154 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c30, some c33, some c21, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p154 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked154 : lratChecker f154 p154 = .success := by decide +kernel
theorem unsat154 : Unsatisfiable (PosFin 29) f154 := by
  apply lratCheckerSound f154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p154
  · intro a ha; simp [p154] at ha; subst a; trivial
  · exact checked154
theorem derived154 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c154 := by
  apply localUnsat_implies_entails f154 [c30, c33, c21] c154 unsat154 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c155 : DefaultClause 29 := directClause [(⟨13, by decide⟩, false), (⟨20, by decide⟩, true), (⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f155 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c108, some c36, some c61, some c152, some c154, some c7, some c27, some c93, some c77, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p155 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked155 : lratChecker f155 p155 = .success := by decide +kernel
theorem unsat155 : Unsatisfiable (PosFin 29) f155 := by
  apply lratCheckerSound f155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p155
  · intro a ha; simp [p155] at ha; subst a; trivial
  · exact checked155
theorem derived155 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c155 := by
  apply localUnsat_implies_entails f155 [c108, c36, c61, c152, c154, c7, c27, c93, c77] c155 unsat155 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c152 := derived152 a h
  have h4 : Entails.eval a c154 := derived154 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c156 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f156 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c71, some c107, some c150, some c155, some c3, some c75, some c125, some c17, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p156 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked156 : lratChecker f156 p156 = .success := by decide +kernel
theorem unsat156 : Unsatisfiable (PosFin 29) f156 := by
  apply lratCheckerSound f156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p156
  · intro a ha; simp [p156] at ha; subst a; trivial
  · exact checked156
theorem derived156 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c156 := by
  apply localUnsat_implies_entails f156 [c71, c107, c150, c155, c3, c75, c125, c17] c156 unsat156 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c150 := derived150 a h
  have h3 : Entails.eval a c155 := derived155 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c125 := h 124 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c157 : DefaultClause 29 := directClause [(⟨20, by decide⟩, true), (⟨13, by decide⟩, true), (⟨26, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f157 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c41, some c75, some c125, some c17, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p157 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked157 : lratChecker f157 p157 = .success := by decide +kernel
theorem unsat157 : Unsatisfiable (PosFin 29) f157 := by
  apply lratCheckerSound f157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p157
  · intro a ha; simp [p157] at ha; subst a; trivial
  · exact checked157
theorem derived157 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c157 := by
  apply localUnsat_implies_entails f157 [c41, c75, c125, c17] c157 unsat157 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c75 := h 74 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c158 : DefaultClause 29 := directClause [(⟨13, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f158 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c156, some c71, some c107, some c61, some c41, some c157, some c37, some c121, some c149, some c147, some c66, some c70, some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p158 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked158 : lratChecker f158 p158 = .success := by decide +kernel
theorem unsat158 : Unsatisfiable (PosFin 29) f158 := by
  apply lratCheckerSound f158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p158
  · intro a ha; simp [p158] at ha; subst a; trivial
  · exact checked158
theorem derived158 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c158 := by
  apply localUnsat_implies_entails f158 [c156, c71, c107, c61, c41, c157, c37, c121, c149, c147, c66, c70] c158 unsat158 (by rfl) a
  have h0 : Entails.eval a c156 := derived156 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c157 := derived157 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c149 := derived149 a h
  have h9 : Entails.eval a c147 := derived147 a h
  have h10 : Entails.eval a c66 := h 65 (by decide)
  have h11 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c159 : DefaultClause 29 := directClause [(⟨17, by decide⟩, true), (⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f159 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c153, some c145, some c87, some c27, some c140, some c30, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p159 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked159 : lratChecker f159 p159 = .success := by decide +kernel
theorem unsat159 : Unsatisfiable (PosFin 29) f159 := by
  apply lratCheckerSound f159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p159
  · intro a ha; simp [p159] at ha; subst a; trivial
  · exact checked159
theorem derived159 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c159 := by
  apply localUnsat_implies_entails f159 [c153, c145, c87, c27, c140, c30] c159 unsat159 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c145 := derived145 a h
  have h2 : Entails.eval a c87 := h 86 (by decide)
  have h3 : Entails.eval a c27 := h 26 (by decide)
  have h4 : Entails.eval a c140 := h 139 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c160 : DefaultClause 29 := directClause [(⟨15, by decide⟩, true), (⟨14, by decide⟩, false), (⟨13, by decide⟩, false), (⟨21, by decide⟩, true), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨26, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f160 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c159, some c35, some c154, some c93, some c7, some c64, some c20, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p160 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked160 : lratChecker f160 p160 = .success := by decide +kernel
theorem unsat160 : Unsatisfiable (PosFin 29) f160 := by
  apply lratCheckerSound f160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p160
  · intro a ha; simp [p160] at ha; subst a; trivial
  · exact checked160
theorem derived160 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c160 := by
  apply localUnsat_implies_entails f160 [c159, c35, c154, c93, c7, c64, c20] c160 unsat160 (by rfl) a
  have h0 : Entails.eval a c159 := derived159 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c154 := derived154 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c161 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false), (⟨18, by decide⟩, true), (⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f161 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c30, some c33, some c124, some c102, some c57, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true))]
def p161 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked161 : lratChecker f161 p161 = .success := by decide +kernel
theorem unsat161 : Unsatisfiable (PosFin 29) f161 := by
  apply lratCheckerSound f161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p161
  · intro a ha; simp [p161] at ha; subst a; trivial
  · exact checked161
theorem derived161 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c161 := by
  apply localUnsat_implies_entails f161 [c30, c33, c124, c102, c57] c161 unsat161 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c162 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f162 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c158, some c156, some c71, some c107, some c61, some c160, some c132, some c161, some c7, some c27, some c138, some c97, some c128, some c44, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p162 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked162 : lratChecker f162 p162 = .success := by decide +kernel
theorem unsat162 : Unsatisfiable (PosFin 29) f162 := by
  apply lratCheckerSound f162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p162
  · intro a ha; simp [p162] at ha; subst a; trivial
  · exact checked162
theorem derived162 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c162 := by
  apply localUnsat_implies_entails f162 [c158, c156, c71, c107, c61, c160, c132, c161, c7, c27, c138, c97, c128, c44] c162 unsat162 (by rfl) a
  have h0 : Entails.eval a c158 := derived158 a h
  have h1 : Entails.eval a c156 := derived156 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c160 := derived160 a h
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c161 := derived161 a h
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c27 := h 26 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c128 := h 127 (by decide)
  have h13 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c163 : DefaultClause 29 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f163 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c156, some c162, some c4, some c65, some c113, some c16, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p163 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked163 : lratChecker f163 p163 = .success := by decide +kernel
theorem unsat163 : Unsatisfiable (PosFin 29) f163 := by
  apply lratCheckerSound f163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p163
  · intro a ha; simp [p163] at ha; subst a; trivial
  · exact checked163
theorem derived163 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c163 := by
  apply localUnsat_implies_entails f163 [c107, c61, c156, c162, c4, c65, c113, c16] c163 unsat163 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c156 := derived156 a h
  have h3 : Entails.eval a c162 := derived162 a h
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c164 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f164 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c4, some c113, some c16, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p164 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked164 : lratChecker f164 p164 = .success := by decide +kernel
theorem unsat164 : Unsatisfiable (PosFin 29) f164 := by
  apply lratCheckerSound f164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p164
  · intro a ha; simp [p164] at ha; subst a; trivial
  · exact checked164
theorem derived164 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c164 := by
  apply localUnsat_implies_entails f164 [c4, c113, c16] c164 unsat164 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c113 := h 112 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c165 : DefaultClause 29 := directClause [(⟨9, by decide⟩, true), (⟨14, by decide⟩, false), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f165 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c6, some c24, some c53, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p165 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked165 : lratChecker f165 p165 = .success := by decide +kernel
theorem unsat165 : Unsatisfiable (PosFin 29) f165 := by
  apply lratCheckerSound f165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p165
  · intro a ha; simp [p165] at ha; subst a; trivial
  · exact checked165
theorem derived165 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c165 := by
  apply localUnsat_implies_entails f165 [c6, c24, c53] c165 unsat165 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c166 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f166 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c164, some c165, some c33, some c44, some c27, some c138, some c114, some c139, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p166 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked166 : lratChecker f166 p166 = .success := by decide +kernel
theorem unsat166 : Unsatisfiable (PosFin 29) f166 := by
  apply lratCheckerSound f166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p166
  · intro a ha; simp [p166] at ha; subst a; trivial
  · exact checked166
theorem derived166 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c166 := by
  apply localUnsat_implies_entails f166 [c107, c61, c164, c165, c33, c44, c27, c138, c114, c139] c166 unsat166 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c164 := derived164 a h
  have h3 : Entails.eval a c165 := derived165 a h
  have h4 : Entails.eval a c33 := h 32 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c138 := h 137 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c167 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨15, by decide⟩, true), (⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f167 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c165, some c153, some c44, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p167 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked167 : lratChecker f167 p167 = .success := by decide +kernel
theorem unsat167 : Unsatisfiable (PosFin 29) f167 := by
  apply lratCheckerSound f167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p167
  · intro a ha; simp [p167] at ha; subst a; trivial
  · exact checked167
theorem derived167 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c167 := by
  apply localUnsat_implies_entails f167 [c107, c61, c165, c153, c44] c167 unsat167 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c165 := derived165 a h
  have h3 : Entails.eval a c153 := derived153 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c168 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false), (⟨23, by decide⟩, true), (⟨26, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f168 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c166, some c108, some c167, some c42, some c16, some c20, some c13, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p168 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked168 : lratChecker f168 p168 = .success := by decide +kernel
theorem unsat168 : Unsatisfiable (PosFin 29) f168 := by
  apply lratCheckerSound f168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p168
  · intro a ha; simp [p168] at ha; subst a; trivial
  · exact checked168
theorem derived168 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c168 := by
  apply localUnsat_implies_entails f168 [c107, c166, c108, c167, c42, c16, c20, c13] c168 unsat168 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c166 := derived166 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c167 := derived167 a h
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c169 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨5, by decide⟩, false), (⟨4, by decide⟩, true), (⟨23, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f169 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c7, some c107, some c62, some c137, some c94, some c89, some c32, some c40, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p169 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked169 : lratChecker f169 p169 = .success := by decide +kernel
theorem unsat169 : Unsatisfiable (PosFin 29) f169 := by
  apply lratCheckerSound f169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p169
  · intro a ha; simp [p169] at ha; subst a; trivial
  · exact checked169
theorem derived169 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c169 := by
  apply localUnsat_implies_entails f169 [c61, c7, c107, c62, c137, c94, c89, c32, c40] c169 unsat169 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c7 := h 6 (by decide)
  have h2 : Entails.eval a c107 := h 106 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c137 := h 136 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c170 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨21, by decide⟩, true), (⟨27, by decide⟩, false), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f170 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c161, some c30, some c33, some c92, some c132, some c21, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true))]
def p170 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked170 : lratChecker f170 p170 = .success := by decide +kernel
theorem unsat170 : Unsatisfiable (PosFin 29) f170 := by
  apply lratCheckerSound f170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p170
  · intro a ha; simp [p170] at ha; subst a; trivial
  · exact checked170
theorem derived170 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c170 := by
  apply localUnsat_implies_entails f170 [c161, c30, c33, c92, c132, c21] c170 unsat170 (by rfl) a
  have h0 : Entails.eval a c161 := derived161 a h
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c92 := h 91 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c171 : DefaultClause 29 := directClause [(⟨24, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f171 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c71, some c61, some c163, some c168, some c7, some c14, some c169, some c65, some c170, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p171 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked171 : lratChecker f171 p171 = .success := by decide +kernel
theorem unsat171 : Unsatisfiable (PosFin 29) f171 := by
  apply lratCheckerSound f171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p171
  · intro a ha; simp [p171] at ha; subst a; trivial
  · exact checked171
theorem derived171 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c171 := by
  apply localUnsat_implies_entails f171 [c71, c61, c163, c168, c7, c14, c169, c65, c170] c171 unsat171 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c163 := derived163 a h
  have h3 : Entails.eval a c168 := derived168 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c169 := derived169 a h
  have h7 : Entails.eval a c65 := h 64 (by decide)
  have h8 : Entails.eval a c170 := derived170 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c172 : DefaultClause 29 := directClause [(⟨14, by decide⟩, false), (⟨11, by decide⟩, false), (⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f172 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c30, some c33, some c25, some c112, some c39, some c55, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p172 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked172 : lratChecker f172 p172 = .success := by decide +kernel
theorem unsat172 : Unsatisfiable (PosFin 29) f172 := by
  apply lratCheckerSound f172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p172
  · intro a ha; simp [p172] at ha; subst a; trivial
  · exact checked172
theorem derived172 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c172 := by
  apply localUnsat_implies_entails f172 [c30, c33, c25, c112, c39, c55] c172 unsat172 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c173 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨21, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f173 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c65, some c164, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p173 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked173 : lratChecker f173 p173 = .success := by decide +kernel
theorem unsat173 : Unsatisfiable (PosFin 29) f173 := by
  apply lratCheckerSound f173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p173
  · intro a ha; simp [p173] at ha; subst a; trivial
  · exact checked173
theorem derived173 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c173 := by
  apply localUnsat_implies_entails f173 [c107, c61, c65, c164] c173 unsat173 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  have h3 : Entails.eval a c164 := derived164 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c174 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f174 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c173, some c172, some c7, some c64, some c16, some c135, some c138, some c132, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p174 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked174 : lratChecker f174 p174 = .success := by decide +kernel
theorem unsat174 : Unsatisfiable (PosFin 29) f174 := by
  apply lratCheckerSound f174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p174
  · intro a ha; simp [p174] at ha; subst a; trivial
  · exact checked174
theorem derived174 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c174 := by
  apply localUnsat_implies_entails f174 [c107, c61, c173, c172, c7, c64, c16, c135, c138, c132] c174 unsat174 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c173 := derived173 a h
  have h3 : Entails.eval a c172 := derived172 a h
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c138 := h 137 (by decide)
  have h9 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c175 : DefaultClause 29 := directClause [(⟨11, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f175 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c171, some c174, some c108, some c62, some c71, some c107, some c61, some c7, some c27, some c138, some c168, some c16, some c88, some c36, some c90, some c106, some c80, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p175 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked175 : lratChecker f175 p175 = .success := by decide +kernel
theorem unsat175 : Unsatisfiable (PosFin 29) f175 := by
  apply lratCheckerSound f175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p175
  · intro a ha; simp [p175] at ha; subst a; trivial
  · exact checked175
theorem derived175 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c175 := by
  apply localUnsat_implies_entails f175 [c171, c174, c108, c62, c71, c107, c61, c7, c27, c138, c168, c16, c88, c36, c90, c106, c80] c175 unsat175 (by rfl) a
  have h0 : Entails.eval a c171 := derived171 a h
  have h1 : Entails.eval a c174 := derived174 a h
  have h2 : Entails.eval a c108 := h 107 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c27 := h 26 (by decide)
  have h9 : Entails.eval a c138 := h 137 (by decide)
  have h10 : Entails.eval a c168 := derived168 a h
  have h11 : Entails.eval a c16 := h 15 (by decide)
  have h12 : Entails.eval a c88 := h 87 (by decide)
  have h13 : Entails.eval a c36 := h 35 (by decide)
  have h14 : Entails.eval a c90 := h 89 (by decide)
  have h15 : Entails.eval a c106 := h 105 (by decide)
  have h16 : Entails.eval a c80 := h 79 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c176 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f176 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c175, some c171, some c174, some c108, some c71, some c61, some c168, some c36, some c154, some c42, some c16, some c84, some c136, some c110, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p176 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked176 : lratChecker f176 p176 = .success := by decide +kernel
theorem unsat176 : Unsatisfiable (PosFin 29) f176 := by
  apply lratCheckerSound f176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p176
  · intro a ha; simp [p176] at ha; subst a; trivial
  · exact checked176
theorem derived176 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c176 := by
  apply localUnsat_implies_entails f176 [c175, c171, c174, c108, c71, c61, c168, c36, c154, c42, c16, c84, c136, c110] c176 unsat176 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c171 := derived171 a h
  have h2 : Entails.eval a c174 := derived174 a h
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c168 := derived168 a h
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c154 := derived154 a h
  have h9 : Entails.eval a c42 := h 41 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c84 := h 83 (by decide)
  have h12 : Entails.eval a c136 := h 135 (by decide)
  have h13 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c177 : DefaultClause 29 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f177 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c71, some c171, some c174, some c62, some c108, some c175, some c176, some c14, some c137, some c169, some c89, some c30, some c36, some c40, some c104, some c127, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p177 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked177 : lratChecker f177 p177 = .success := by decide +kernel
theorem unsat177 : Unsatisfiable (PosFin 29) f177 := by
  apply lratCheckerSound f177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p177
  · intro a ha; simp [p177] at ha; subst a; trivial
  · exact checked177
theorem derived177 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c177 := by
  apply localUnsat_implies_entails f177 [c107, c61, c71, c171, c174, c62, c108, c175, c176, c14, c137, c169, c89, c30, c36, c40, c104, c127] c177 unsat177 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c171 := derived171 a h
  have h4 : Entails.eval a c174 := derived174 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c175 := derived175 a h
  have h8 : Entails.eval a c176 := derived176 a h
  have h9 : Entails.eval a c14 := h 13 (by decide)
  have h10 : Entails.eval a c137 := h 136 (by decide)
  have h11 : Entails.eval a c169 := derived169 a h
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c30 := h 29 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c40 := h 39 (by decide)
  have h16 : Entails.eval a c104 := h 103 (by decide)
  have h17 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c178 : DefaultClause 29 := directClause [(⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨21, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f178 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c108, some c62, some c177, some c107, some c61, some c15, some c137, some c147, some c42, some c54, some c39, some c32, some c81, some c49, some c86, some c115, some c116, some c100, some c111, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p178 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked178 : lratChecker f178 p178 = .success := by decide +kernel
theorem unsat178 : Unsatisfiable (PosFin 29) f178 := by
  apply lratCheckerSound f178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p178
  · intro a ha; simp [p178] at ha; subst a; trivial
  · exact checked178
theorem derived178 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c178 := by
  apply localUnsat_implies_entails f178 [c108, c62, c177, c107, c61, c15, c137, c147, c42, c54, c39, c32, c81, c49, c86, c115, c116, c100, c111] c178 unsat178 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c177 := derived177 a h
  have h3 : Entails.eval a c107 := h 106 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c15 := h 14 (by decide)
  have h6 : Entails.eval a c137 := h 136 (by decide)
  have h7 : Entails.eval a c147 := derived147 a h
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c39 := h 38 (by decide)
  have h11 : Entails.eval a c32 := h 31 (by decide)
  have h12 : Entails.eval a c81 := h 80 (by decide)
  have h13 : Entails.eval a c49 := h 48 (by decide)
  have h14 : Entails.eval a c86 := h 85 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c116 := h 115 (by decide)
  have h17 : Entails.eval a c100 := h 99 (by decide)
  have h18 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c179 : DefaultClause 29 := directClause [(⟨10, by decide⟩, true), (⟨4, by decide⟩, false), (⟨11, by decide⟩, false), (⟨15, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f179 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c177, some c61, some c40, some c18, some c39, some c33, some c42, some c16, some c84, some c100, some c111, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p179 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked179 : lratChecker f179 p179 = .success := by decide +kernel
theorem unsat179 : Unsatisfiable (PosFin 29) f179 := by
  apply lratCheckerSound f179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p179
  · intro a ha; simp [p179] at ha; subst a; trivial
  · exact checked179
theorem derived179 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c179 := by
  apply localUnsat_implies_entails f179 [c177, c61, c40, c18, c39, c33, c42, c16, c84, c100, c111] c179 unsat179 (by rfl) a
  have h0 : Entails.eval a c177 := derived177 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c18 := h 17 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  have h5 : Entails.eval a c33 := h 32 (by decide)
  have h6 : Entails.eval a c42 := h 41 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c100 := h 99 (by decide)
  have h10 : Entails.eval a c111 := h 110 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c180 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false), (⟨21, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f180 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c108, some c62, some c177, some c178, some c179, some c32, some c39, some c20, some c42, some c147, some c154, some c30, some c76, some c95, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p180 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked180 : lratChecker f180 p180 = .success := by decide +kernel
theorem unsat180 : Unsatisfiable (PosFin 29) f180 := by
  apply lratCheckerSound f180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p180
  · intro a ha; simp [p180] at ha; subst a; trivial
  · exact checked180
theorem derived180 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c180 := by
  apply localUnsat_implies_entails f180 [c108, c62, c177, c178, c179, c32, c39, c20, c42, c147, c154, c30, c76, c95] c180 unsat180 (by rfl) a
  have h0 : Entails.eval a c108 := h 107 (by decide)
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c177 := derived177 a h
  have h3 : Entails.eval a c178 := derived178 a h
  have h4 : Entails.eval a c179 := derived179 a h
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c147 := derived147 a h
  have h10 : Entails.eval a c154 := derived154 a h
  have h11 : Entails.eval a c30 := h 29 (by decide)
  have h12 : Entails.eval a c76 := h 75 (by decide)
  have h13 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c181 : DefaultClause 29 := directClause [(⟨21, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f181 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c107, some c61, some c62, some c108, some c180, some c7, some c138, some c16, some c42, some c44, some c167, some c39, some c36, some c53, some c21, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p181 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked181 : lratChecker f181 p181 = .success := by decide +kernel
theorem unsat181 : Unsatisfiable (PosFin 29) f181 := by
  apply lratCheckerSound f181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p181
  · intro a ha; simp [p181] at ha; subst a; trivial
  · exact checked181
theorem derived181 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c181 := by
  apply localUnsat_implies_entails f181 [c107, c61, c62, c108, c180, c7, c138, c16, c42, c44, c167, c39, c36, c53, c21] c181 unsat181 (by rfl) a
  have h0 : Entails.eval a c107 := h 106 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c62 := h 61 (by decide)
  have h3 : Entails.eval a c108 := h 107 (by decide)
  have h4 : Entails.eval a c180 := derived180 a h
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c16 := h 15 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c44 := h 43 (by decide)
  have h10 : Entails.eval a c167 := derived167 a h
  have h11 : Entails.eval a c39 := h 38 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  have h13 : Entails.eval a c53 := h 52 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c182 : DefaultClause 29 := directClause [(⟨11, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f182 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c181, some c177, some c61, some c7, some c28, some c64, some c16, some c58, some c38, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p182 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked182 : lratChecker f182 p182 = .success := by decide +kernel
theorem unsat182 : Unsatisfiable (PosFin 29) f182 := by
  apply lratCheckerSound f182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p182
  · intro a ha; simp [p182] at ha; subst a; trivial
  · exact checked182
theorem derived182 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c182 := by
  apply localUnsat_implies_entails f182 [c181, c177, c61, c7, c28, c64, c16, c58, c38] c182 unsat182 (by rfl) a
  have h0 : Entails.eval a c181 := derived181 a h
  have h1 : Entails.eval a c177 := derived177 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c183 : DefaultClause 29 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f183 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c61, some c107, some c177, some c181, some c173, some c182, some c30, some c33, some c5, some c112, some c57, some c47, some c15, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p183 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked183 : lratChecker f183 p183 = .success := by decide +kernel
theorem unsat183 : Unsatisfiable (PosFin 29) f183 := by
  apply lratCheckerSound f183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p183
  · intro a ha; simp [p183] at ha; subst a; trivial
  · exact checked183
theorem derived183 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c183 := by
  apply localUnsat_implies_entails f183 [c61, c107, c177, c181, c173, c182, c30, c33, c5, c112, c57, c47, c15] c183 unsat183 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c107 := h 106 (by decide)
  have h2 : Entails.eval a c177 := derived177 a h
  have h3 : Entails.eval a c181 := derived181 a h
  have h4 : Entails.eval a c173 := derived173 a h
  have h5 : Entails.eval a c182 := derived182 a h
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c33 := h 32 (by decide)
  have h8 : Entails.eval a c5 := h 4 (by decide)
  have h9 : Entails.eval a c112 := h 111 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c47 := h 46 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c184 : DefaultClause 29 := directClause [(⟨8, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f184 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c38, some c49, some c39, some c55, some c40, some c19, some c52, some c26, some c23, some c144, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p184 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked184 : lratChecker f184 p184 = .success := by decide +kernel
theorem unsat184 : Unsatisfiable (PosFin 29) f184 := by
  apply lratCheckerSound f184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p184
  · intro a ha; simp [p184] at ha; subst a; trivial
  · exact checked184
theorem derived184 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c184 := by
  apply localUnsat_implies_entails f184 [c183, c38, c49, c39, c55, c40, c19, c52, c26, c23, c144] c184 unsat184 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c185 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨21, by decide⟩, true), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f185 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c184, some c30, some c54, some c63, some c39, some c92, some c132, some c49, some c10, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p185 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked185 : lratChecker f185 p185 = .success := by decide +kernel
theorem unsat185 : Unsatisfiable (PosFin 29) f185 := by
  apply lratCheckerSound f185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p185
  · intro a ha; simp [p185] at ha; subst a; trivial
  · exact checked185
theorem derived185 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c185 := by
  apply localUnsat_implies_entails f185 [c183, c184, c30, c54, c63, c39, c92, c132, c49, c10] c185 unsat185 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c184 := derived184 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c63 := h 62 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c186 : DefaultClause 29 := directClause [(⟨4, by decide⟩, true), (⟨11, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f186 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c185, some c42, some c30, some c38, some c117, some c47, some c121, some c132, some c11, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p186 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked186 : lratChecker f186 p186 = .success := by decide +kernel
theorem unsat186 : Unsatisfiable (PosFin 29) f186 := by
  apply lratCheckerSound f186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p186
  · intro a ha; simp [p186] at ha; subst a; trivial
  · exact checked186
theorem derived186 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c186 := by
  apply localUnsat_implies_entails f186 [c183, c185, c42, c30, c38, c117, c47, c121, c132, c11] c186 unsat186 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c185 := derived185 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c121 := h 120 (by decide)
  have h8 : Entails.eval a c132 := h 131 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c187 : DefaultClause 29 := directClause [(⟨7, by decide⟩, true), (⟨11, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f187 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c42, some c30, some c33, some c38, some c117, some c112, some c47, some c132, some c133, some c120, some c95, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p187 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked187 : lratChecker f187 p187 = .success := by decide +kernel
theorem unsat187 : Unsatisfiable (PosFin 29) f187 := by
  apply lratCheckerSound f187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p187
  · intro a ha; simp [p187] at ha; subst a; trivial
  · exact checked187
theorem derived187 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c187 := by
  apply localUnsat_implies_entails f187 [c183, c42, c30, c33, c38, c117, c112, c47, c132, c133, c120, c95] c187 unsat187 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c38 := h 37 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c47 := h 46 (by decide)
  have h8 : Entails.eval a c132 := h 131 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c188 : DefaultClause 29 := directClause [(⟨11, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f188 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c186, some c187, some c16, some c20, some c38, some c43, some c58, some c164, some c29, some c120, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p188 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked188 : lratChecker f188 p188 = .success := by decide +kernel
theorem unsat188 : Unsatisfiable (PosFin 29) f188 := by
  apply lratCheckerSound f188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p188
  · intro a ha; simp [p188] at ha; subst a; trivial
  · exact checked188
theorem derived188 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c188 := by
  apply localUnsat_implies_entails f188 [c183, c186, c187, c16, c20, c38, c43, c58, c164, c29, c120] c188 unsat188 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c186 := derived186 a h
  have h2 : Entails.eval a c187 := derived187 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c164 := derived164 a h
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c189 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f189 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c188, some c113, some c109, some c120, some c134, some c29, some c58, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p189 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked189 : lratChecker f189 p189 = .success := by decide +kernel
theorem unsat189 : Unsatisfiable (PosFin 29) f189 := by
  apply lratCheckerSound f189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p189
  · intro a ha; simp [p189] at ha; subst a; trivial
  · exact checked189
theorem derived189 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c189 := by
  apply localUnsat_implies_entails f189 [c183, c188, c113, c109, c120, c134, c29, c58] c189 unsat189 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c188 := derived188 a h
  have h2 : Entails.eval a c113 := h 112 (by decide)
  have h3 : Entails.eval a c109 := h 108 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c29 := h 28 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c190 : DefaultClause 29 := directClause [(⟨25, by decide⟩, true), (⟨27, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f190 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c7, some c28, some c58, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p190 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked190 : lratChecker f190 p190 = .success := by decide +kernel
theorem unsat190 : Unsatisfiable (PosFin 29) f190 := by
  apply lratCheckerSound f190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p190
  · intro a ha; simp [p190] at ha; subst a; trivial
  · exact checked190
theorem derived190 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c190 := by
  apply localUnsat_implies_entails f190 [c7, c28, c58] c190 unsat190 (by rfl) a
  have h0 : Entails.eval a c7 := h 6 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c191 : DefaultClause 29 := directClause [(⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f191 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c188, some c190, some c91, some c131, some c13, some c138, some c20, some c132, some c73, some c122, some c83, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p191 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked191 : lratChecker f191 p191 = .success := by decide +kernel
theorem unsat191 : Unsatisfiable (PosFin 29) f191 := by
  apply lratCheckerSound f191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p191
  · intro a ha; simp [p191] at ha; subst a; trivial
  · exact checked191
theorem derived191 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c191 := by
  apply localUnsat_implies_entails f191 [c188, c190, c91, c131, c13, c138, c20, c132, c73, c122, c83] c191 unsat191 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c190 := derived190 a h
  have h2 : Entails.eval a c91 := h 90 (by decide)
  have h3 : Entails.eval a c131 := h 130 (by decide)
  have h4 : Entails.eval a c13 := h 12 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c192 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true), (⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f192 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c188, some c189, some c191, some c71, some c120, some c138, some c92, some c132, some c153, some c136, some c10, some c91, some c79, some c142, some c123, some c126, some c141, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p192 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked192 : lratChecker f192 p192 = .success := by decide +kernel
theorem unsat192 : Unsatisfiable (PosFin 29) f192 := by
  apply lratCheckerSound f192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p192
  · intro a ha; simp [p192] at ha; subst a; trivial
  · exact checked192
theorem derived192 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c192 := by
  apply localUnsat_implies_entails f192 [c188, c189, c191, c71, c120, c138, c92, c132, c153, c136, c10, c91, c79, c142, c123, c126, c141] c192 unsat192 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c189 := derived189 a h
  have h2 : Entails.eval a c191 := derived191 a h
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c153 := derived153 a h
  have h9 : Entails.eval a c136 := h 135 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c91 := h 90 (by decide)
  have h12 : Entails.eval a c79 := h 78 (by decide)
  have h13 : Entails.eval a c142 := h 141 (by decide)
  have h14 : Entails.eval a c123 := h 122 (by decide)
  have h15 : Entails.eval a c126 := h 125 (by decide)
  have h16 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c193 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false), (⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f193 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c188, some c192, some c16, some c50, some c7, some c2, some c51, some c9, some c17, some c98, some c56, some c78, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p193 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked193 : lratChecker f193 p193 = .success := by decide +kernel
theorem unsat193 : Unsatisfiable (PosFin 29) f193 := by
  apply lratCheckerSound f193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p193
  · intro a ha; simp [p193] at ha; subst a; trivial
  · exact checked193
theorem derived193 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c193 := by
  apply localUnsat_implies_entails f193 [c188, c192, c16, c50, c7, c2, c51, c9, c17, c98, c56, c78] c193 unsat193 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c192 := derived192 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c2 := h 1 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c17 := h 16 (by decide)
  have h9 : Entails.eval a c98 := h 97 (by decide)
  have h10 : Entails.eval a c56 := h 55 (by decide)
  have h11 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c194 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f194 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c188, some c193, some c38, some c16, some c50, some c7, some c2, some c51, some c9, some c17, some c45, some c130, some c143, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p194 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked194 : lratChecker f194 p194 = .success := by decide +kernel
theorem unsat194 : Unsatisfiable (PosFin 29) f194 := by
  apply lratCheckerSound f194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p194
  · intro a ha; simp [p194] at ha; subst a; trivial
  · exact checked194
theorem derived194 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c194 := by
  apply localUnsat_implies_entails f194 [c188, c193, c38, c16, c50, c7, c2, c51, c9, c17, c45, c130, c143] c194 unsat194 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c193 := derived193 a h
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c7 := h 6 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c9 := h 8 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c130 := h 129 (by decide)
  have h12 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c195 : DefaultClause 29 := directClause [(⟨4, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f195 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c194, some c188, some c64, some c131, some c112, some c67, some c132, some c42, some c56, some c59, some c60, some c9, some c12, some c68, some c82, some c118, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p195 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked195 : lratChecker f195 p195 = .success := by decide +kernel
theorem unsat195 : Unsatisfiable (PosFin 29) f195 := by
  apply lratCheckerSound f195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p195
  · intro a ha; simp [p195] at ha; subst a; trivial
  · exact checked195
theorem derived195 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c195 := by
  apply localUnsat_implies_entails f195 [c183, c194, c188, c64, c131, c112, c67, c132, c42, c56, c59, c60, c9, c12, c68, c82, c118] c195 unsat195 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c194 := derived194 a h
  have h2 : Entails.eval a c188 := derived188 a h
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  have h5 : Entails.eval a c112 := h 111 (by decide)
  have h6 : Entails.eval a c67 := h 66 (by decide)
  have h7 : Entails.eval a c132 := h 131 (by decide)
  have h8 : Entails.eval a c42 := h 41 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c60 := h 59 (by decide)
  have h12 : Entails.eval a c9 := h 8 (by decide)
  have h13 : Entails.eval a c12 := h 11 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c118 := h 117 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c196 : DefaultClause 29 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f196 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c188, some c194, some c42, some c64, some c91, some c131, some c112, some c195, some c53, some c165, some c44, some c13, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p196 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked196 : lratChecker f196 p196 = .success := by decide +kernel
theorem unsat196 : Unsatisfiable (PosFin 29) f196 := by
  apply lratCheckerSound f196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p196
  · intro a ha; simp [p196] at ha; subst a; trivial
  · exact checked196
theorem derived196 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c196 := by
  apply localUnsat_implies_entails f196 [c188, c194, c42, c64, c91, c131, c112, c195, c53, c165, c44, c13] c196 unsat196 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c194 := derived194 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c91 := h 90 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c195 := derived195 a h
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c165 := derived165 a h
  have h10 : Entails.eval a c44 := h 43 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c197 : DefaultClause 29 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f197 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c196, some c62, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p197 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked197 : lratChecker f197 p197 = .success := by decide +kernel
theorem unsat197 : Unsatisfiable (PosFin 29) f197 := by
  apply lratCheckerSound f197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p197
  · intro a ha; simp [p197] at ha; subst a; trivial
  · exact checked197
theorem derived197 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c197 := by
  apply localUnsat_implies_entails f197 [c196, c62] c197 unsat197 (by rfl) a
  have h0 : Entails.eval a c196 := derived196 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c198 : DefaultClause 29 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f198 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c196, some c108, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p198 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked198 : lratChecker f198 p198 = .success := by decide +kernel
theorem unsat198 : Unsatisfiable (PosFin 29) f198 := by
  apply lratCheckerSound f198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p198
  · intro a ha; simp [p198] at ha; subst a; trivial
  · exact checked198
theorem derived198 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c198 := by
  apply localUnsat_implies_entails f198 [c196, c108] c198 unsat198 (by rfl) a
  have h0 : Entails.eval a c196 := derived196 a h
  have h1 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c199 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f199 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c198, some c197, some c138, some c135, some c131, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p199 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked199 : lratChecker f199 p199 = .success := by decide +kernel
theorem unsat199 : Unsatisfiable (PosFin 29) f199 := by
  apply lratCheckerSound f199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p199
  · intro a ha; simp [p199] at ha; subst a; trivial
  · exact checked199
theorem derived199 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c199 := by
  apply localUnsat_implies_entails f199 [c198, c197, c138, c135, c131] c199 unsat199 (by rfl) a
  have h0 : Entails.eval a c198 := derived198 a h
  have h1 : Entails.eval a c197 := derived197 a h
  have h2 : Entails.eval a c138 := h 137 (by decide)
  have h3 : Entails.eval a c135 := h 134 (by decide)
  have h4 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c200 : DefaultClause 29 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f200 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c197, some c67, some c2, some c16, some c199, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p200 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked200 : lratChecker f200 p200 = .success := by decide +kernel
theorem unsat200 : Unsatisfiable (PosFin 29) f200 := by
  apply lratCheckerSound f200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p200
  · intro a ha; simp [p200] at ha; subst a; trivial
  · exact checked200
theorem derived200 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c200 := by
  apply localUnsat_implies_entails f200 [c183, c197, c67, c2, c16, c199] c200 unsat200 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c197 := derived197 a h
  have h2 : Entails.eval a c67 := h 66 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c199 := derived199 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c201 : DefaultClause 29 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f201 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c183, some c198, some c200, some c38, some c109, some c30, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p201 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked201 : lratChecker f201 p201 = .success := by decide +kernel
theorem unsat201 : Unsatisfiable (PosFin 29) f201 := by
  apply lratCheckerSound f201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p201
  · intro a ha; simp [p201] at ha; subst a; trivial
  · exact checked201
theorem derived201 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c201 := by
  apply localUnsat_implies_entails f201 [c183, c198, c200, c38, c109, c30] c201 unsat201 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c198 := derived198 a h
  have h2 : Entails.eval a c200 := derived200 a h
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c202 : DefaultClause 29 := directClause [(⟨7, by decide⟩, false), (⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f202 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c200, some c201, some c197, some c16, some c49, some c94, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p202 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked202 : lratChecker f202 p202 = .success := by decide +kernel
theorem unsat202 : Unsatisfiable (PosFin 29) f202 := by
  apply lratCheckerSound f202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p202
  · intro a ha; simp [p202] at ha; subst a; trivial
  · exact checked202
theorem derived202 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c202 := by
  apply localUnsat_implies_entails f202 [c200, c201, c197, c16, c49, c94] c202 unsat202 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c201 := derived201 a h
  have h2 : Entails.eval a c197 := derived197 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c203 : DefaultClause 29 := directClause [(⟨7, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f203 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c198, some c183, some c200, some c42, some c117, some c30, some (DefaultClause.unit (⟨7, by decide⟩, false))]
def p203 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked203 : lratChecker f203 p203 = .success := by decide +kernel
theorem unsat203 : Unsatisfiable (PosFin 29) f203 := by
  apply lratCheckerSound f203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p203
  · intro a ha; simp [p203] at ha; subst a; trivial
  · exact checked203
theorem derived203 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c203 := by
  apply localUnsat_implies_entails f203 [c198, c183, c200, c42, c117, c30] c203 unsat203 (by rfl) a
  have h0 : Entails.eval a c198 := derived198 a h
  have h1 : Entails.eval a c183 := derived183 a h
  have h2 : Entails.eval a c200 := derived200 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c204 : DefaultClause 29 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f204 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c203, some c201, some c16, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p204 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked204 : lratChecker f204 p204 = .success := by decide +kernel
theorem unsat204 : Unsatisfiable (PosFin 29) f204 := by
  apply lratCheckerSound f204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p204
  · intro a ha; simp [p204] at ha; subst a; trivial
  · exact checked204
theorem derived204 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c204 := by
  apply localUnsat_implies_entails f204 [c203, c201, c16] c204 unsat204 (by rfl) a
  have h0 : Entails.eval a c203 := derived203 a h
  have h1 : Entails.eval a c201 := derived201 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c205 : DefaultClause 29 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f205 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c203, some c202, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p205 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked205 : lratChecker f205 p205 = .success := by decide +kernel
theorem unsat205 : Unsatisfiable (PosFin 29) f205 := by
  apply lratCheckerSound f205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p205
  · intro a ha; simp [p205] at ha; subst a; trivial
  · exact checked205
theorem derived205 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c205 := by
  apply localUnsat_implies_entails f205 [c203, c202] c205 unsat205 (by rfl) a
  have h0 : Entails.eval a c203 := derived203 a h
  have h1 : Entails.eval a c202 := derived202 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c206 : DefaultClause 29 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f206 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c204, some c197, some c183, some c63, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p206 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked206 : lratChecker f206 p206 = .success := by decide +kernel
theorem unsat206 : Unsatisfiable (PosFin 29) f206 := by
  apply lratCheckerSound f206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p206
  · intro a ha; simp [p206] at ha; subst a; trivial
  · exact checked206
theorem derived206 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c206 := by
  apply localUnsat_implies_entails f206 [c204, c197, c183, c63] c206 unsat206 (by rfl) a
  have h0 : Entails.eval a c204 := derived204 a h
  have h1 : Entails.eval a c197 := derived197 a h
  have h2 : Entails.eval a c183 := derived183 a h
  have h3 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c207 : DefaultClause 29 := directClause [(⟨25, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f207 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c205, some c91, some (DefaultClause.unit (⟨25, by decide⟩, true))]
def p207 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2]]
theorem checked207 : lratChecker f207 p207 = .success := by decide +kernel
theorem unsat207 : Unsatisfiable (PosFin 29) f207 := by
  apply lratCheckerSound f207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p207
  · intro a ha; simp [p207] at ha; subst a; trivial
  · exact checked207
theorem derived207 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c207 := by
  apply localUnsat_implies_entails f207 [c205, c91] c207 unsat207 (by rfl) a
  have h0 : Entails.eval a c205 := derived205 a h
  have h1 : Entails.eval a c91 := h 90 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c208 : DefaultClause 29 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f208 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c206, some c200, some c30, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p208 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked208 : lratChecker f208 p208 = .success := by decide +kernel
theorem unsat208 : Unsatisfiable (PosFin 29) f208 := by
  apply lratCheckerSound f208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p208
  · intro a ha; simp [p208] at ha; subst a; trivial
  · exact checked208
theorem derived208 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c208 := by
  apply localUnsat_implies_entails f208 [c206, c200, c30] c208 unsat208 (by rfl) a
  have h0 : Entails.eval a c206 := derived206 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c209 : DefaultClause 29 := directClause [] (by decide +kernel) (by decide +kernel)
def f209 : DefaultFormula 29 := DefaultFormula.ofArray #[none, some c207, some c208, some c198, some c204, some c140]
def p209 : List (Action (DefaultClause 29) (PosFin 29)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked209 : lratChecker f209 p209 = .success := by decide +kernel
theorem unsat209 : Unsatisfiable (PosFin 29) f209 := by
  apply lratCheckerSound f209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p209
  · intro a ha; simp [p209] at ha; subst a; trivial
  · exact checked209
theorem derived209 (a : PosFin 29 → Bool) (h : InputSat a) : Entails.eval a c209 := by
  apply localUnsat_implies_entails f209 [c207, c208, c198, c204, c140] c209 unsat209 (by rfl) a
  have h0 : Entails.eval a c207 := derived207 a h
  have h1 : Entails.eval a c208 := derived208 a h
  have h2 : Entails.eval a c198 := derived198 a h
  have h3 : Entails.eval a c204 := derived204 a h
  have h4 : Entails.eval a c140 := h 139 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived209

end CochromaticTwenty.Certificates.Z12Direct_4_0_7
