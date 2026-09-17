import MerLeanExperiment.Certificates.Z12Direct_5_5_1.Inputs

/-! Generated from the actual pinned z12direct_5_5_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c144 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨16, by decide⟩, true), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f144 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c38, some c80, some c2, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p144 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked144 : lratChecker f144 p144 = .success := by decide +kernel
theorem unsat144 : Unsatisfiable (PosFin 31) f144 := by
  apply lratCheckerSound f144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p144
  · intro a ha; simp [p144] at ha; subst a; trivial
  · exact checked144
theorem derived144 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c144 := by
  apply localUnsat_implies_entails f144 [c38, c80, c2] c144 unsat144 (by rfl) a
  have h0 : Entails.eval a c38 := h 37 (by decide)
  have h1 : Entails.eval a c80 := h 79 (by decide)
  have h2 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c145 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f145 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c60, some c67, some c54, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p145 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked145 : lratChecker f145 p145 = .success := by decide +kernel
theorem unsat145 : Unsatisfiable (PosFin 31) f145 := by
  apply lratCheckerSound f145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p145
  · intro a ha; simp [p145] at ha; subst a; trivial
  · exact checked145
theorem derived145 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c145 := by
  apply localUnsat_implies_entails f145 [c60, c67, c54] c145 unsat145 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c67 := h 66 (by decide)
  have h2 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c146 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f146 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c16, some c145, some c2, some c23, some c29, some c18, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p146 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked146 : lratChecker f146 p146 = .success := by decide +kernel
theorem unsat146 : Unsatisfiable (PosFin 31) f146 := by
  apply lratCheckerSound f146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p146
  · intro a ha; simp [p146] at ha; subst a; trivial
  · exact checked146
theorem derived146 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c146 := by
  apply localUnsat_implies_entails f146 [c16, c145, c2, c23, c29, c18] c146 unsat146 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c145 := derived145 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c23 := h 22 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c147 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f147 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c146, some c20, some c57, some c14, some c11, some c103, some c109, some c13, some c10, some c5, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p147 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked147 : lratChecker f147 p147 = .success := by decide +kernel
theorem unsat147 : Unsatisfiable (PosFin 31) f147 := by
  apply lratCheckerSound f147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p147
  · intro a ha; simp [p147] at ha; subst a; trivial
  · exact checked147
theorem derived147 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c147 := by
  apply localUnsat_implies_entails f147 [c146, c20, c57, c14, c11, c103, c109, c13, c10, c5] c147 unsat147 (by rfl) a
  have h0 : Entails.eval a c146 := derived146 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c11 := h 10 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c109 := h 108 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c10 := h 9 (by decide)
  have h9 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c148 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f148 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c147, some c141, some c146, some c17, some c28, some c46, some c27, some c129, some c143, some c140, some c106, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p148 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked148 : lratChecker f148 p148 = .success := by decide +kernel
theorem unsat148 : Unsatisfiable (PosFin 31) f148 := by
  apply lratCheckerSound f148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p148
  · intro a ha; simp [p148] at ha; subst a; trivial
  · exact checked148
theorem derived148 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c148 := by
  apply localUnsat_implies_entails f148 [c147, c141, c146, c17, c28, c46, c27, c129, c143, c140, c106] c148 unsat148 (by rfl) a
  have h0 : Entails.eval a c147 := derived147 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c146 := derived146 a h
  have h3 : Entails.eval a c17 := h 16 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c149 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨10, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f149 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c146, some c2, some c148, some c21, some c34, some c100, some c26, some c64, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p149 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked149 : lratChecker f149 p149 = .success := by decide +kernel
theorem unsat149 : Unsatisfiable (PosFin 31) f149 := by
  apply lratCheckerSound f149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p149
  · intro a ha; simp [p149] at ha; subst a; trivial
  · exact checked149
theorem derived149 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c149 := by
  apply localUnsat_implies_entails f149 [c146, c2, c148, c21, c34, c100, c26, c64] c149 unsat149 (by rfl) a
  have h0 : Entails.eval a c146 := derived146 a h
  have h1 : Entails.eval a c2 := h 1 (by decide)
  have h2 : Entails.eval a c148 := derived148 a h
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c100 := h 99 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c150 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f150 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c147, some c141, some c146, some c11, some c61, some c77, some c70, some c78, some c76, some c3, some c79, some c66, some c132, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p150 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked150 : lratChecker f150 p150 = .success := by decide +kernel
theorem unsat150 : Unsatisfiable (PosFin 31) f150 := by
  apply lratCheckerSound f150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p150
  · intro a ha; simp [p150] at ha; subst a; trivial
  · exact checked150
theorem derived150 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c150 := by
  apply localUnsat_implies_entails f150 [c147, c141, c146, c11, c61, c77, c70, c78, c76, c3, c79, c66, c132] c150 unsat150 (by rfl) a
  have h0 : Entails.eval a c147 := derived147 a h
  have h1 : Entails.eval a c141 := h 140 (by decide)
  have h2 : Entails.eval a c146 := derived146 a h
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c77 := h 76 (by decide)
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c78 := h 77 (by decide)
  have h8 : Entails.eval a c76 := h 75 (by decide)
  have h9 : Entails.eval a c3 := h 2 (by decide)
  have h10 : Entails.eval a c79 := h 78 (by decide)
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c151 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f151 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c146, some c147, some c141, some c150, some c148, some c149, some c100, some c14, some c64, some c52, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p151 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked151 : lratChecker f151 p151 = .success := by decide +kernel
theorem unsat151 : Unsatisfiable (PosFin 31) f151 := by
  apply lratCheckerSound f151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p151
  · intro a ha; simp [p151] at ha; subst a; trivial
  · exact checked151
theorem derived151 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c151 := by
  apply localUnsat_implies_entails f151 [c146, c147, c141, c150, c148, c149, c100, c14, c64, c52] c151 unsat151 (by rfl) a
  have h0 : Entails.eval a c146 := derived146 a h
  have h1 : Entails.eval a c147 := derived147 a h
  have h2 : Entails.eval a c141 := h 140 (by decide)
  have h3 : Entails.eval a c150 := derived150 a h
  have h4 : Entails.eval a c148 := derived148 a h
  have h5 : Entails.eval a c149 := derived149 a h
  have h6 : Entails.eval a c100 := h 99 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c152 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f152 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c142, some c39, some c32, some c3, some c20, some c36, some c118, some c102, some c122, some c124, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p152 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked152 : lratChecker f152 p152 = .success := by decide +kernel
theorem unsat152 : Unsatisfiable (PosFin 31) f152 := by
  apply lratCheckerSound f152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p152
  · intro a ha; simp [p152] at ha; subst a; trivial
  · exact checked152
theorem derived152 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c152 := by
  apply localUnsat_implies_entails f152 [c151, c142, c39, c32, c3, c20, c36, c118, c102, c122, c124] c152 unsat152 (by rfl) a
  have h0 : Entails.eval a c151 := derived151 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c39 := h 38 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c118 := h 117 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c122 := h 121 (by decide)
  have h10 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c153 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨16, by decide⟩, false), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f153 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c142, some c3, some c20, some c36, some c53, some c89, some c62, some c122, some c125, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p153 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked153 : lratChecker f153 p153 = .success := by decide +kernel
theorem unsat153 : Unsatisfiable (PosFin 31) f153 := by
  apply lratCheckerSound f153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p153
  · intro a ha; simp [p153] at ha; subst a; trivial
  · exact checked153
theorem derived153 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c153 := by
  apply localUnsat_implies_entails f153 [c151, c142, c3, c20, c36, c53, c89, c62, c122, c125] c153 unsat153 (by rfl) a
  have h0 : Entails.eval a c151 := derived151 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c62 := h 61 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c154 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f154 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c152, some c151, some c142, some c2, some c153, some c109, some c48, some c25, some c35, some c134, some c138, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p154 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked154 : lratChecker f154 p154 = .success := by decide +kernel
theorem unsat154 : Unsatisfiable (PosFin 31) f154 := by
  apply lratCheckerSound f154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p154
  · intro a ha; simp [p154] at ha; subst a; trivial
  · exact checked154
theorem derived154 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c154 := by
  apply localUnsat_implies_entails f154 [c152, c151, c142, c2, c153, c109, c48, c25, c35, c134, c138] c154 unsat154 (by rfl) a
  have h0 : Entails.eval a c152 := derived152 a h
  have h1 : Entails.eval a c151 := derived151 a h
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c153 := derived153 a h
  have h5 : Entails.eval a c109 := h 108 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c155 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f155 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c142, some c154, some c81, some c72, some c57, some c76, some c141, some c122, some c77, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p155 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked155 : lratChecker f155 p155 = .success := by decide +kernel
theorem unsat155 : Unsatisfiable (PosFin 31) f155 := by
  apply lratCheckerSound f155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p155
  · intro a ha; simp [p155] at ha; subst a; trivial
  · exact checked155
theorem derived155 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c155 := by
  apply localUnsat_implies_entails f155 [c151, c142, c154, c81, c72, c57, c76, c141, c122, c77] c155 unsat155 (by rfl) a
  have h0 : Entails.eval a c151 := derived151 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c154 := derived154 a h
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c141 := h 140 (by decide)
  have h8 : Entails.eval a c122 := h 121 (by decide)
  have h9 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c156 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f156 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c155, some c151, some c142, some c67, some c80, some c75, some c1, some c29, some c33, some c133, some c137, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p156 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked156 : lratChecker f156 p156 = .success := by decide +kernel
theorem unsat156 : Unsatisfiable (PosFin 31) f156 := by
  apply lratCheckerSound f156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p156
  · intro a ha; simp [p156] at ha; subst a; trivial
  · exact checked156
theorem derived156 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c156 := by
  apply localUnsat_implies_entails f156 [c155, c151, c142, c67, c80, c75, c1, c29, c33, c133, c137] c156 unsat156 (by rfl) a
  have h0 : Entails.eval a c155 := derived155 a h
  have h1 : Entails.eval a c151 := derived151 a h
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c67 := h 66 (by decide)
  have h4 : Entails.eval a c80 := h 79 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c29 := h 28 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c137 := h 136 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c157 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f157 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c142, some c155, some c156, some c73, some c65, some c144, some c2, some c29, some c35, some c134, some c138, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p157 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked157 : lratChecker f157 p157 = .success := by decide +kernel
theorem unsat157 : Unsatisfiable (PosFin 31) f157 := by
  apply lratCheckerSound f157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p157
  · intro a ha; simp [p157] at ha; subst a; trivial
  · exact checked157
theorem derived157 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c157 := by
  apply localUnsat_implies_entails f157 [c151, c142, c155, c156, c73, c65, c144, c2, c29, c35, c134, c138] c157 unsat157 (by rfl) a
  have h0 : Entails.eval a c151 := derived151 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c155 := derived155 a h
  have h3 : Entails.eval a c156 := derived156 a h
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c65 := h 64 (by decide)
  have h6 : Entails.eval a c144 := derived144 a h
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c29 := h 28 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c134 := h 133 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c158 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f158 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c15, some c144, some c75, some c35, some c88, some c47, some c2, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p158 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked158 : lratChecker f158 p158 = .success := by decide +kernel
theorem unsat158 : Unsatisfiable (PosFin 31) f158 := by
  apply lratCheckerSound f158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p158
  · intro a ha; simp [p158] at ha; subst a; trivial
  · exact checked158
theorem derived158 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c158 := by
  apply localUnsat_implies_entails f158 [c15, c144, c75, c35, c88, c47, c2] c158 unsat158 (by rfl) a
  have h0 : Entails.eval a c15 := h 14 (by decide)
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c75 := h 74 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c159 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f159 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c139, some c158, some c142, some c93, some c91, some c65, some c8, some c2, some c23, some c47, some c127, some c1, some c87, some c130, some c105, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p159 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked159 : lratChecker f159 p159 = .success := by decide +kernel
theorem unsat159 : Unsatisfiable (PosFin 31) f159 := by
  apply lratCheckerSound f159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p159
  · intro a ha; simp [p159] at ha; subst a; trivial
  · exact checked159
theorem derived159 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c159 := by
  apply localUnsat_implies_entails f159 [c157, c139, c158, c142, c93, c91, c65, c8, c2, c23, c47, c127, c1, c87, c130, c105] c159 unsat159 (by rfl) a
  have h0 : Entails.eval a c157 := derived157 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c158 := derived158 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c65 := h 64 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c23 := h 22 (by decide)
  have h10 : Entails.eval a c47 := h 46 (by decide)
  have h11 : Entails.eval a c127 := h 126 (by decide)
  have h12 : Entails.eval a c1 := h 0 (by decide)
  have h13 : Entails.eval a c87 := h 86 (by decide)
  have h14 : Entails.eval a c130 := h 129 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c160 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f160 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c139, some c158, some c142, some c159, some c60, some c88, some c1, some c47, some c101, some c51, some c108, some c126, some c111, some c110, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p160 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked160 : lratChecker f160 p160 = .success := by decide +kernel
theorem unsat160 : Unsatisfiable (PosFin 31) f160 := by
  apply lratCheckerSound f160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p160
  · intro a ha; simp [p160] at ha; subst a; trivial
  · exact checked160
theorem derived160 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c160 := by
  apply localUnsat_implies_entails f160 [c157, c139, c158, c142, c159, c60, c88, c1, c47, c101, c51, c108, c126, c111, c110] c160 unsat160 (by rfl) a
  have h0 : Entails.eval a c157 := derived157 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c158 := derived158 a h
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c159 := derived159 a h
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c47 := h 46 (by decide)
  have h9 : Entails.eval a c101 := h 100 (by decide)
  have h10 : Entails.eval a c51 := h 50 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c126 := h 125 (by decide)
  have h13 : Entails.eval a c111 := h 110 (by decide)
  have h14 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c161 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f161 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c160, some c57, some c78, some c141, some c77, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p161 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked161 : lratChecker f161 p161 = .success := by decide +kernel
theorem unsat161 : Unsatisfiable (PosFin 31) f161 := by
  apply lratCheckerSound f161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p161
  · intro a ha; simp [p161] at ha; subst a; trivial
  · exact checked161
theorem derived161 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c161 := by
  apply localUnsat_implies_entails f161 [c160, c57, c78, c141, c77] c161 unsat161 (by rfl) a
  have h0 : Entails.eval a c160 := derived160 a h
  have h1 : Entails.eval a c57 := h 56 (by decide)
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c162 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f162 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c161, some c142, some c160, some c61, some c72, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p162 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked162 : lratChecker f162 p162 = .success := by decide +kernel
theorem unsat162 : Unsatisfiable (PosFin 31) f162 := by
  apply lratCheckerSound f162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p162
  · intro a ha; simp [p162] at ha; subst a; trivial
  · exact checked162
theorem derived162 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c162 := by
  apply localUnsat_implies_entails f162 [c161, c142, c160, c61, c72] c162 unsat162 (by rfl) a
  have h0 : Entails.eval a c161 := derived161 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  have h2 : Entails.eval a c160 := derived160 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c163 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨4, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f163 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c160, some c157, some c139, some c64, some c28, some c120, some c99, some c20, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p163 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked163 : lratChecker f163 p163 = .success := by decide +kernel
theorem unsat163 : Unsatisfiable (PosFin 31) f163 := by
  apply lratCheckerSound f163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p163
  · intro a ha; simp [p163] at ha; subst a; trivial
  · exact checked163
theorem derived163 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c163 := by
  apply localUnsat_implies_entails f163 [c160, c157, c139, c64, c28, c120, c99, c20] c163 unsat163 (by rfl) a
  have h0 : Entails.eval a c160 := derived160 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  have h5 : Entails.eval a c120 := h 119 (by decide)
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c164 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f164 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c160, some c157, some c139, some c142, some c161, some c162, some c163, some c83, some c84, some c24, some c68, some c82, some c116, some c1, some c7, some c115, some c30, some c104, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p164 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked164 : lratChecker f164 p164 = .success := by decide +kernel
theorem unsat164 : Unsatisfiable (PosFin 31) f164 := by
  apply lratCheckerSound f164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p164
  · intro a ha; simp [p164] at ha; subst a; trivial
  · exact checked164
theorem derived164 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c164 := by
  apply localUnsat_implies_entails f164 [c160, c157, c139, c142, c161, c162, c163, c83, c84, c24, c68, c82, c116, c1, c7, c115, c30, c104] c164 unsat164 (by rfl) a
  have h0 : Entails.eval a c160 := derived160 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c142 := h 141 (by decide)
  have h4 : Entails.eval a c161 := derived161 a h
  have h5 : Entails.eval a c162 := derived162 a h
  have h6 : Entails.eval a c163 := derived163 a h
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c68 := h 67 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c116 := h 115 (by decide)
  have h13 : Entails.eval a c1 := h 0 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c115 := h 114 (by decide)
  have h16 : Entails.eval a c30 := h 29 (by decide)
  have h17 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c165 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨15, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f165 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c164, some c157, some c139, some c83, some c84, some c89, some c82, some c75, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p165 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked165 : lratChecker f165 p165 = .success := by decide +kernel
theorem unsat165 : Unsatisfiable (PosFin 31) f165 := by
  apply lratCheckerSound f165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p165
  · intro a ha; simp [p165] at ha; subst a; trivial
  · exact checked165
theorem derived165 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c165 := by
  apply localUnsat_implies_entails f165 [c164, c157, c139, c83, c84, c89, c82, c75] c165 unsat165 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c83 := h 82 (by decide)
  have h4 : Entails.eval a c84 := h 83 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c166 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f166 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c164, some c160, some c157, some c139, some c165, some c3, some c41, some c42, some c40, some c48, some c35, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p166 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked166 : lratChecker f166 p166 = .success := by decide +kernel
theorem unsat166 : Unsatisfiable (PosFin 31) f166 := by
  apply lratCheckerSound f166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p166
  · intro a ha; simp [p166] at ha; subst a; trivial
  · exact checked166
theorem derived166 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c166 := by
  apply localUnsat_implies_entails f166 [c164, c160, c157, c139, c165, c3, c41, c42, c40, c48, c35] c166 unsat166 (by rfl) a
  have h0 : Entails.eval a c164 := derived164 a h
  have h1 : Entails.eval a c160 := derived160 a h
  have h2 : Entails.eval a c157 := derived157 a h
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c165 := derived165 a h
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c167 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f167 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c139, some c160, some c164, some c166, some c64, some c28, some c112, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p167 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked167 : lratChecker f167 p167 = .success := by decide +kernel
theorem unsat167 : Unsatisfiable (PosFin 31) f167 := by
  apply lratCheckerSound f167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p167
  · intro a ha; simp [p167] at ha; subst a; trivial
  · exact checked167
theorem derived167 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c167 := by
  apply localUnsat_implies_entails f167 [c157, c139, c160, c164, c166, c64, c28, c112] c167 unsat167 (by rfl) a
  have h0 : Entails.eval a c157 := derived157 a h
  have h1 : Entails.eval a c139 := h 138 (by decide)
  have h2 : Entails.eval a c160 := derived160 a h
  have h3 : Entails.eval a c164 := derived164 a h
  have h4 : Entails.eval a c166 := derived166 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c168 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f168 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c135, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p168 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked168 : lratChecker f168 p168 = .success := by decide +kernel
theorem unsat168 : Unsatisfiable (PosFin 31) f168 := by
  apply lratCheckerSound f168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p168
  · intro a ha; simp [p168] at ha; subst a; trivial
  · exact checked168
theorem derived168 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c168 := by
  apply localUnsat_implies_entails f168 [c167, c135] c168 unsat168 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c169 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f169 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c90, some c86, some c77, some c6, some c141, some c59, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p169 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked169 : lratChecker f169 p169 = .success := by decide +kernel
theorem unsat169 : Unsatisfiable (PosFin 31) f169 := by
  apply lratCheckerSound f169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p169
  · intro a ha; simp [p169] at ha; subst a; trivial
  · exact checked169
theorem derived169 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c169 := by
  apply localUnsat_implies_entails f169 [c168, c90, c86, c77, c6, c141, c59] c169 unsat169 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c170 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f170 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c158, some c80, some c139, some c67, some c145, some c1, some c98, some c113, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p170 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked170 : lratChecker f170 p170 = .success := by decide +kernel
theorem unsat170 : Unsatisfiable (PosFin 31) f170 := by
  apply lratCheckerSound f170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p170
  · intro a ha; simp [p170] at ha; subst a; trivial
  · exact checked170
theorem derived170 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c170 := by
  apply localUnsat_implies_entails f170 [c167, c158, c80, c139, c67, c145, c1, c98, c113] c170 unsat170 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c158 := derived158 a h
  have h2 : Entails.eval a c80 := h 79 (by decide)
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c145 := derived145 a h
  have h6 : Entails.eval a c1 := h 0 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c171 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨4, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f171 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c170, some c58, some c61, some c169, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p171 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked171 : lratChecker f171 p171 = .success := by decide +kernel
theorem unsat171 : Unsatisfiable (PosFin 31) f171 := by
  apply lratCheckerSound f171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p171
  · intro a ha; simp [p171] at ha; subst a; trivial
  · exact checked171
theorem derived171 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c171 := by
  apply localUnsat_implies_entails f171 [c167, c170, c58, c61, c169] c171 unsat171 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c170 := derived170 a h
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c169 := derived169 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c172 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨4, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f172 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c9, some c92, some c119, some c139, some c63, some c81, some c4, some c85, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p172 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked172 : lratChecker f172 p172 = .success := by decide +kernel
theorem unsat172 : Unsatisfiable (PosFin 31) f172 := by
  apply lratCheckerSound f172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p172
  · intro a ha; simp [p172] at ha; subst a; trivial
  · exact checked172
theorem derived172 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c172 := by
  apply localUnsat_implies_entails f172 [c168, c9, c92, c119, c139, c63, c81, c4, c85] c172 unsat172 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c9 := h 8 (by decide)
  have h2 : Entails.eval a c92 := h 91 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  have h7 : Entails.eval a c4 := h 3 (by decide)
  have h8 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c173 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f173 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c171, some c172, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p173 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked173 : lratChecker f173 p173 = .success := by decide +kernel
theorem unsat173 : Unsatisfiable (PosFin 31) f173 := by
  apply lratCheckerSound f173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p173
  · intro a ha; simp [p173] at ha; subst a; trivial
  · exact checked173
theorem derived173 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c173 := by
  apply localUnsat_implies_entails f173 [c171, c172] c173 unsat173 (by rfl) a
  have h0 : Entails.eval a c171 := derived171 a h
  have h1 : Entails.eval a c172 := derived172 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c174 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f174 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c173, some c158, some c139, some c73, some c63, some c85, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p174 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked174 : lratChecker f174 p174 = .success := by decide +kernel
theorem unsat174 : Unsatisfiable (PosFin 31) f174 := by
  apply lratCheckerSound f174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p174
  · intro a ha; simp [p174] at ha; subst a; trivial
  · exact checked174
theorem derived174 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c174 := by
  apply localUnsat_implies_entails f174 [c168, c173, c158, c139, c73, c63, c85] c174 unsat174 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c173 := derived173 a h
  have h2 : Entails.eval a c158 := derived158 a h
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c175 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f175 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c173, some c2, some c96, some c89, some c62, some c95, some c75, some c136, some c131, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p175 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked175 : lratChecker f175 p175 = .success := by decide +kernel
theorem unsat175 : Unsatisfiable (PosFin 31) f175 := by
  apply lratCheckerSound f175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p175
  · intro a ha; simp [p175] at ha; subst a; trivial
  · exact checked175
theorem derived175 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c175 := by
  apply localUnsat_implies_entails f175 [c167, c173, c2, c96, c89, c62, c95, c75, c136, c131] c175 unsat175 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c173 := derived173 a h
  have h2 : Entails.eval a c2 := h 1 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c75 := h 74 (by decide)
  have h8 : Entails.eval a c136 := h 135 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c176 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f176 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c175, some c174, some c39, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p176 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked176 : lratChecker f176 p176 = .success := by decide +kernel
theorem unsat176 : Unsatisfiable (PosFin 31) f176 := by
  apply lratCheckerSound f176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p176
  · intro a ha; simp [p176] at ha; subst a; trivial
  · exact checked176
theorem derived176 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c176 := by
  apply localUnsat_implies_entails f176 [c175, c174, c39] c176 unsat176 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c174 := derived174 a h
  have h2 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c177 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f177 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c49, some c45, some c37, some c12, some c141, some c22, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p177 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked177 : lratChecker f177 p177 = .success := by decide +kernel
theorem unsat177 : Unsatisfiable (PosFin 31) f177 := by
  apply lratCheckerSound f177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p177
  · intro a ha; simp [p177] at ha; subst a; trivial
  · exact checked177
theorem derived177 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c177 := by
  apply localUnsat_implies_entails f177 [c168, c49, c45, c37, c12, c141, c22] c177 unsat177 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c45 := h 44 (by decide)
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c178 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨5, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f178 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c118, some c176, some c50, some c177, some c158, some c38, some c139, some c1, some c29, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p178 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked178 : lratChecker f178 p178 = .success := by decide +kernel
theorem unsat178 : Unsatisfiable (PosFin 31) f178 := by
  apply lratCheckerSound f178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p178
  · intro a ha; simp [p178] at ha; subst a; trivial
  · exact checked178
theorem derived178 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c178 := by
  apply localUnsat_implies_entails f178 [c168, c118, c176, c50, c177, c158, c38, c139, c1, c29] c178 unsat178 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c118 := h 117 (by decide)
  have h2 : Entails.eval a c176 := derived176 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c177 := derived177 a h
  have h5 : Entails.eval a c158 := derived158 a h
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c179 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f179 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c175, some c178, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p179 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked179 : lratChecker f179 p179 = .success := by decide +kernel
theorem unsat179 : Unsatisfiable (PosFin 31) f179 := by
  apply lratCheckerSound f179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p179
  · intro a ha; simp [p179] at ha; subst a; trivial
  · exact checked179
theorem derived179 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c179 := by
  apply localUnsat_implies_entails f179 [c175, c178] c179 unsat179 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c178 := derived178 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c180 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f180 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c179, some c3, some c98, some c97, some c158, some c136, some c131, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p180 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked180 : lratChecker f180 p180 = .success := by decide +kernel
theorem unsat180 : Unsatisfiable (PosFin 31) f180 := by
  apply lratCheckerSound f180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p180
  · intro a ha; simp [p180] at ha; subst a; trivial
  · exact checked180
theorem derived180 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c180 := by
  apply localUnsat_implies_entails f180 [c167, c179, c3, c98, c97, c158, c136, c131] c180 unsat180 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c179 := derived179 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c97 := h 96 (by decide)
  have h5 : Entails.eval a c158 := derived158 a h
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c181 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f181 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c180, some c179, some c121, some c117, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p181 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked181 : lratChecker f181 p181 = .success := by decide +kernel
theorem unsat181 : Unsatisfiable (PosFin 31) f181 := by
  apply lratCheckerSound f181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p181
  · intro a ha; simp [p181] at ha; subst a; trivial
  · exact checked181
theorem derived181 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c181 := by
  apply localUnsat_implies_entails f181 [c168, c180, c179, c121, c117] c181 unsat181 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c180 := derived180 a h
  have h2 : Entails.eval a c179 := derived179 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c182 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f182 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c167, some c173, some c179, some c180, some c181, some c2, some c96, some c94, some c95, some c107, some c85, some c69, some c71, some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p182 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked182 : lratChecker f182 p182 = .success := by decide +kernel
theorem unsat182 : Unsatisfiable (PosFin 31) f182 := by
  apply lratCheckerSound f182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p182
  · intro a ha; simp [p182] at ha; subst a; trivial
  · exact checked182
theorem derived182 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c182 := by
  apply localUnsat_implies_entails f182 [c168, c167, c173, c179, c180, c181, c2, c96, c94, c95, c107, c85, c69, c71] c182 unsat182 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c167 := derived167 a h
  have h2 : Entails.eval a c173 := derived173 a h
  have h3 : Entails.eval a c179 := derived179 a h
  have h4 : Entails.eval a c180 := derived180 a h
  have h5 : Entails.eval a c181 := derived181 a h
  have h6 : Entails.eval a c2 := h 1 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c94 := h 93 (by decide)
  have h9 : Entails.eval a c95 := h 94 (by decide)
  have h10 : Entails.eval a c107 := h 106 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c183 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f183 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c182, some c142, some (DefaultClause.unit (⟨28, by decide⟩, false))]
def p183 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked183 : lratChecker f183 p183 = .success := by decide +kernel
theorem unsat183 : Unsatisfiable (PosFin 31) f183 := by
  apply lratCheckerSound f183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p183
  · intro a ha; simp [p183] at ha; subst a; trivial
  · exact checked183
theorem derived183 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c183 := by
  apply localUnsat_implies_entails f183 [c182, c142] c183 unsat183 (by rfl) a
  have h0 : Entails.eval a c182 := derived182 a h
  have h1 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c184 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f184 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c182, some c167, some c183, some c168, some c77, some c56, some c123, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p184 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked184 : lratChecker f184 p184 = .success := by decide +kernel
theorem unsat184 : Unsatisfiable (PosFin 31) f184 := by
  apply lratCheckerSound f184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p184
  · intro a ha; simp [p184] at ha; subst a; trivial
  · exact checked184
theorem derived184 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c184 := by
  apply localUnsat_implies_entails f184 [c182, c167, c183, c168, c77, c56, c123] c184 unsat184 (by rfl) a
  have h0 : Entails.eval a c182 := derived182 a h
  have h1 : Entails.eval a c167 := derived167 a h
  have h2 : Entails.eval a c183 := derived183 a h
  have h3 : Entails.eval a c168 := derived168 a h
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c185 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f185 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c183, some c168, some c184, some c74, some c85, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p185 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked185 : lratChecker f185 p185 = .success := by decide +kernel
theorem unsat185 : Unsatisfiable (PosFin 31) f185 := by
  apply lratCheckerSound f185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p185
  · intro a ha; simp [p185] at ha; subst a; trivial
  · exact checked185
theorem derived185 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c185 := by
  apply localUnsat_implies_entails f185 [c183, c168, c184, c74, c85] c185 unsat185 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c168 := derived168 a h
  have h2 : Entails.eval a c184 := derived184 a h
  have h3 : Entails.eval a c74 := h 73 (by decide)
  have h4 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c186 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f186 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c183, some c184, some c146, some c139, some c185, some c19, some c55, some c23, some c47, some c88, some c1, some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p186 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked186 : lratChecker f186 p186 = .success := by decide +kernel
theorem unsat186 : Unsatisfiable (PosFin 31) f186 := by
  apply lratCheckerSound f186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p186
  · intro a ha; simp [p186] at ha; subst a; trivial
  · exact checked186
theorem derived186 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c186 := by
  apply localUnsat_implies_entails f186 [c167, c183, c184, c146, c139, c185, c19, c55, c23, c47, c88, c1] c186 unsat186 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c183 := derived183 a h
  have h2 : Entails.eval a c184 := derived184 a h
  have h3 : Entails.eval a c146 := derived146 a h
  have h4 : Entails.eval a c139 := h 138 (by decide)
  have h5 : Entails.eval a c185 := derived185 a h
  have h6 : Entails.eval a c19 := h 18 (by decide)
  have h7 : Entails.eval a c55 := h 54 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c187 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f187 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c183, some c186, some c146, some c139, some c105, some c23, some c114, some c1, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p187 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked187 : lratChecker f187 p187 = .success := by decide +kernel
theorem unsat187 : Unsatisfiable (PosFin 31) f187 := by
  apply lratCheckerSound f187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p187
  · intro a ha; simp [p187] at ha; subst a; trivial
  · exact checked187
theorem derived187 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c187 := by
  apply localUnsat_implies_entails f187 [c183, c186, c146, c139, c105, c23, c114, c1] c187 unsat187 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c186 := derived186 a h
  have h2 : Entails.eval a c146 := derived146 a h
  have h3 : Entails.eval a c139 := h 138 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c114 := h 113 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c188 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f188 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c183, some c167, some c168, some c186, some c146, some c139, some c187, some c116, some c96, some c119, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p188 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked188 : lratChecker f188 p188 = .success := by decide +kernel
theorem unsat188 : Unsatisfiable (PosFin 31) f188 := by
  apply lratCheckerSound f188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p188
  · intro a ha; simp [p188] at ha; subst a; trivial
  · exact checked188
theorem derived188 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c188 := by
  apply localUnsat_implies_entails f188 [c183, c167, c168, c186, c146, c139, c187, c116, c96, c119] c188 unsat188 (by rfl) a
  have h0 : Entails.eval a c183 := derived183 a h
  have h1 : Entails.eval a c167 := derived167 a h
  have h2 : Entails.eval a c168 := derived168 a h
  have h3 : Entails.eval a c186 := derived186 a h
  have h4 : Entails.eval a c146 := derived146 a h
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c187 := derived187 a h
  have h7 : Entails.eval a c116 := h 115 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c189 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f189 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c188, some c167, some c168, some c186, some c116, some c44, some c119, some c115, some c43, some c96, some c31, some c95, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p189 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked189 : lratChecker f189 p189 = .success := by decide +kernel
theorem unsat189 : Unsatisfiable (PosFin 31) f189 := by
  apply lratCheckerSound f189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p189
  · intro a ha; simp [p189] at ha; subst a; trivial
  · exact checked189
theorem derived189 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c189 := by
  apply localUnsat_implies_entails f189 [c188, c167, c168, c186, c116, c44, c119, c115, c43, c96, c31, c95] c189 unsat189 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c167 := derived167 a h
  have h2 : Entails.eval a c168 := derived168 a h
  have h3 : Entails.eval a c186 := derived186 a h
  have h4 : Entails.eval a c116 := h 115 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c43 := h 42 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c190 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f190 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c186, some c182, some c167, some c183, some c189, some c139, some c11, some c95, some c123, some c131, some c128, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p190 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked190 : lratChecker f190 p190 = .success := by decide +kernel
theorem unsat190 : Unsatisfiable (PosFin 31) f190 := by
  apply lratCheckerSound f190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p190
  · intro a ha; simp [p190] at ha; subst a; trivial
  · exact checked190
theorem derived190 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c190 := by
  apply localUnsat_implies_entails f190 [c186, c182, c167, c183, c189, c139, c11, c95, c123, c131, c128] c190 unsat190 (by rfl) a
  have h0 : Entails.eval a c186 := derived186 a h
  have h1 : Entails.eval a c182 := derived182 a h
  have h2 : Entails.eval a c167 := derived167 a h
  have h3 : Entails.eval a c183 := derived183 a h
  have h4 : Entails.eval a c189 := derived189 a h
  have h5 : Entails.eval a c139 := h 138 (by decide)
  have h6 : Entails.eval a c11 := h 10 (by decide)
  have h7 : Entails.eval a c95 := h 94 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c191 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f191 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c190, some c183, some c188, some c24, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p191 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked191 : lratChecker f191 p191 = .success := by decide +kernel
theorem unsat191 : Unsatisfiable (PosFin 31) f191 := by
  apply lratCheckerSound f191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p191
  · intro a ha; simp [p191] at ha; subst a; trivial
  · exact checked191
theorem derived191 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c191 := by
  apply localUnsat_implies_entails f191 [c190, c183, c188, c24] c191 unsat191 (by rfl) a
  have h0 : Entails.eval a c190 := derived190 a h
  have h1 : Entails.eval a c183 := derived183 a h
  have h2 : Entails.eval a c188 := derived188 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c192 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f192 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c191, some c190, some c168, some c50, some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p192 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked192 : lratChecker f192 p192 = .success := by decide +kernel
theorem unsat192 : Unsatisfiable (PosFin 31) f192 := by
  apply lratCheckerSound f192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p192
  · intro a ha; simp [p192] at ha; subst a; trivial
  · exact checked192
theorem derived192 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c192 := by
  apply localUnsat_implies_entails f192 [c191, c190, c168, c50] c192 unsat192 (by rfl) a
  have h0 : Entails.eval a c191 := derived191 a h
  have h1 : Entails.eval a c190 := derived190 a h
  have h2 : Entails.eval a c168 := derived168 a h
  have h3 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c193 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f193 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c192, some c191, some c188, some c177]
def p193 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked193 : lratChecker f193 p193 = .success := by decide +kernel
theorem unsat193 : Unsatisfiable (PosFin 31) f193 := by
  apply lratCheckerSound f193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p193
  · intro a ha; simp [p193] at ha; subst a; trivial
  · exact checked193
theorem derived193 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c193 := by
  apply localUnsat_implies_entails f193 [c192, c191, c188, c177] c193 unsat193 (by rfl) a
  have h0 : Entails.eval a c192 := derived192 a h
  have h1 : Entails.eval a c191 := derived191 a h
  have h2 : Entails.eval a c188 := derived188 a h
  have h3 : Entails.eval a c177 := derived177 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived193

end CochromaticTwenty.Certificates.Z12Direct_5_5_1
