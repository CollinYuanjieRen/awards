import MerLeanExperiment.Certificates.Z12Direct_5_1_6.Inputs

/-! Generated from the actual pinned z12direct_5_1_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_1_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c126 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨17, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f126 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c116, some c123, some c34, some c51, some c22, some c25, some c78, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p126 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked126 : lratChecker f126 p126 = .success := by decide +kernel
theorem unsat126 : Unsatisfiable (PosFin 31) f126 := by
  apply lratCheckerSound f126 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p126
  · intro a ha; simp [p126] at ha; subst a; trivial
  · exact checked126
theorem derived126 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c126 := by
  apply localUnsat_implies_entails f126 [c116, c123, c34, c51, c22, c25, c78] c126 unsat126 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  have h5 : Entails.eval a c25 := h 24 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c127 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f127 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c116, some c105, some c20, some c6, some c77, some c89, some c72, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p127 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked127 : lratChecker f127 p127 = .success := by decide +kernel
theorem unsat127 : Unsatisfiable (PosFin 31) f127 := by
  apply lratCheckerSound f127 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p127
  · intro a ha; simp [p127] at ha; subst a; trivial
  · exact checked127
theorem derived127 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c127 := by
  apply localUnsat_implies_entails f127 [c116, c105, c20, c6, c77, c89, c72] c127 unsat127 (by rfl) a
  have h0 : Entails.eval a c116 := h 115 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c77 := h 76 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c128 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f128 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c109, some c105, some c127, some c25, some c7, some c21, some c79, some c86, some c70, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p128 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked128 : lratChecker f128 p128 = .success := by decide +kernel
theorem unsat128 : Unsatisfiable (PosFin 31) f128 := by
  apply lratCheckerSound f128 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p128
  · intro a ha; simp [p128] at ha; subst a; trivial
  · exact checked128
theorem derived128 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c128 := by
  apply localUnsat_implies_entails f128 [c109, c105, c127, c25, c7, c21, c79, c86, c70] c128 unsat128 (by rfl) a
  have h0 : Entails.eval a c109 := h 108 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c127 := derived127 a h
  have h3 : Entails.eval a c25 := h 24 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  have h8 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c129 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f129 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c128, some c117, some c109, some c105, some c7, some c21, some c39, some c79, some c86, some c120, some c69, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p129 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked129 : lratChecker f129 p129 = .success := by decide +kernel
theorem unsat129 : Unsatisfiable (PosFin 31) f129 := by
  apply lratCheckerSound f129 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p129
  · intro a ha; simp [p129] at ha; subst a; trivial
  · exact checked129
theorem derived129 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c129 := by
  apply localUnsat_implies_entails f129 [c128, c117, c109, c105, c7, c21, c39, c79, c86, c120, c69] c129 unsat129 (by rfl) a
  have h0 : Entails.eval a c128 := derived128 a h
  have h1 : Entails.eval a c117 := h 116 (by decide)
  have h2 : Entails.eval a c109 := h 108 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c7 := h 6 (by decide)
  have h5 : Entails.eval a c21 := h 20 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  have h7 : Entails.eval a c79 := h 78 (by decide)
  have h8 : Entails.eval a c86 := h 85 (by decide)
  have h9 : Entails.eval a c120 := h 119 (by decide)
  have h10 : Entails.eval a c69 := h 68 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c130 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f130 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c129, some c79, some c86, some c2, some c4, some c50, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p130 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked130 : lratChecker f130 p130 = .success := by decide +kernel
theorem unsat130 : Unsatisfiable (PosFin 31) f130 := by
  apply lratCheckerSound f130 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p130
  · intro a ha; simp [p130] at ha; subst a; trivial
  · exact checked130
theorem derived130 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c130 := by
  apply localUnsat_implies_entails f130 [c129, c79, c86, c2, c4, c50] c130 unsat130 (by rfl) a
  have h0 : Entails.eval a c129 := derived129 a h
  have h1 : Entails.eval a c79 := h 78 (by decide)
  have h2 : Entails.eval a c86 := h 85 (by decide)
  have h3 : Entails.eval a c2 := h 1 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c131 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f131 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c129, some c28, some c128, some c117, some c109, some c130, some c56, some c107, some c120, some c113, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p131 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked131 : lratChecker f131 p131 = .success := by decide +kernel
theorem unsat131 : Unsatisfiable (PosFin 31) f131 := by
  apply lratCheckerSound f131 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p131
  · intro a ha; simp [p131] at ha; subst a; trivial
  · exact checked131
theorem derived131 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c131 := by
  apply localUnsat_implies_entails f131 [c129, c28, c128, c117, c109, c130, c56, c107, c120, c113] c131 unsat131 (by rfl) a
  have h0 : Entails.eval a c129 := derived129 a h
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c128 := derived128 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c130 := derived130 a h
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c107 := h 106 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c132 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f132 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c129, some c105, some c131, some c8, some c82, some c83, some c81, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p132 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked132 : lratChecker f132 p132 = .success := by decide +kernel
theorem unsat132 : Unsatisfiable (PosFin 31) f132 := by
  apply lratCheckerSound f132 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p132
  · intro a ha; simp [p132] at ha; subst a; trivial
  · exact checked132
theorem derived132 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c132 := by
  apply localUnsat_implies_entails f132 [c129, c105, c131, c8, c82, c83, c81] c132 unsat132 (by rfl) a
  have h0 : Entails.eval a c129 := derived129 a h
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c131 := derived131 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c133 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨10, by decide⟩, true), (⟨16, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f133 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c8, some c42, some c20, some c100, some c65, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p133 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked133 : lratChecker f133 p133 = .success := by decide +kernel
theorem unsat133 : Unsatisfiable (PosFin 31) f133 := by
  apply lratCheckerSound f133 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p133
  · intro a ha; simp [p133] at ha; subst a; trivial
  · exact checked133
theorem derived133 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c133 := by
  apply localUnsat_implies_entails f133 [c8, c42, c20, c100, c65] c133 unsat133 (by rfl) a
  have h0 : Entails.eval a c8 := h 7 (by decide)
  have h1 : Entails.eval a c42 := h 41 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c134 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f134 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c105, some c128, some c117, some c132, some c133, some c129, some c82, some c88, some c81, some c2, some c4, some c49, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p134 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked134 : lratChecker f134 p134 = .success := by decide +kernel
theorem unsat134 : Unsatisfiable (PosFin 31) f134 := by
  apply lratCheckerSound f134 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p134
  · intro a ha; simp [p134] at ha; subst a; trivial
  · exact checked134
theorem derived134 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c134 := by
  apply localUnsat_implies_entails f134 [c105, c128, c117, c132, c133, c129, c82, c88, c81, c2, c4, c49] c134 unsat134 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c128 := derived128 a h
  have h2 : Entails.eval a c117 := h 116 (by decide)
  have h3 : Entails.eval a c132 := derived132 a h
  have h4 : Entails.eval a c133 := derived133 a h
  have h5 : Entails.eval a c129 := derived129 a h
  have h6 : Entails.eval a c82 := h 81 (by decide)
  have h7 : Entails.eval a c88 := h 87 (by decide)
  have h8 : Entails.eval a c81 := h 80 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c4 := h 3 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c135 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f135 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c105, some c109, some c128, some c117, some c132, some c133, some c134, some c10, some c78, some c79, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p135 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked135 : lratChecker f135 p135 = .success := by decide +kernel
theorem unsat135 : Unsatisfiable (PosFin 31) f135 := by
  apply lratCheckerSound f135 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p135
  · intro a ha; simp [p135] at ha; subst a; trivial
  · exact checked135
theorem derived135 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c135 := by
  apply localUnsat_implies_entails f135 [c105, c109, c128, c117, c132, c133, c134, c10, c78, c79] c135 unsat135 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c128 := derived128 a h
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c132 := derived132 a h
  have h5 : Entails.eval a c133 := derived133 a h
  have h6 : Entails.eval a c134 := derived134 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c78 := h 77 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c136 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨12, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f136 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c110, some c105, some c58, some c124, some c57, some c123, some c23, some c59, some c35, some c18, some c103, some c102, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p136 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked136 : lratChecker f136 p136 = .success := by decide +kernel
theorem unsat136 : Unsatisfiable (PosFin 31) f136 := by
  apply lratCheckerSound f136 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p136
  · intro a ha; simp [p136] at ha; subst a; trivial
  · exact checked136
theorem derived136 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c136 := by
  apply localUnsat_implies_entails f136 [c135, c110, c105, c58, c124, c57, c123, c23, c59, c35, c18, c103, c102] c136 unsat136 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c105 := h 104 (by decide)
  have h3 : Entails.eval a c58 := h 57 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c57 := h 56 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c18 := h 17 (by decide)
  have h11 : Entails.eval a c103 := h 102 (by decide)
  have h12 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c137 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨12, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f137 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c136, some c135, some c110, some c105, some c81, some c24, some c27, some c83, some c120, some c84, some c43, some c1, some c44, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p137 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked137 : lratChecker f137 p137 = .success := by decide +kernel
theorem unsat137 : Unsatisfiable (PosFin 31) f137 := by
  apply lratCheckerSound f137 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p137
  · intro a ha; simp [p137] at ha; subst a; trivial
  · exact checked137
theorem derived137 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c137 := by
  apply localUnsat_implies_entails f137 [c136, c135, c110, c105, c81, c24, c27, c83, c120, c84, c43, c1, c44] c137 unsat137 (by rfl) a
  have h0 : Entails.eval a c136 := derived136 a h
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  have h5 : Entails.eval a c24 := h 23 (by decide)
  have h6 : Entails.eval a c27 := h 26 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c44 := h 43 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c138 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f138 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c135, some c110, some c136, some c137, some c26, some c47, some c23, some c82, some c124, some c31, some c114, some c1, some c119, some c46, some c115, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p138 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked138 : lratChecker f138 p138 = .success := by decide +kernel
theorem unsat138 : Unsatisfiable (PosFin 31) f138 := by
  apply lratCheckerSound f138 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p138
  · intro a ha; simp [p138] at ha; subst a; trivial
  · exact checked138
theorem derived138 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c138 := by
  apply localUnsat_implies_entails f138 [c135, c110, c136, c137, c26, c47, c23, c82, c124, c31, c114, c1, c119, c46, c115] c138 unsat138 (by rfl) a
  have h0 : Entails.eval a c135 := derived135 a h
  have h1 : Entails.eval a c110 := h 109 (by decide)
  have h2 : Entails.eval a c136 := derived136 a h
  have h3 : Entails.eval a c137 := derived137 a h
  have h4 : Entails.eval a c26 := h 25 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c114 := h 113 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c119 := h 118 (by decide)
  have h13 : Entails.eval a c46 := h 45 (by decide)
  have h14 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c139 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f139 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c105, some c135, some c110, some c138, some c8, some c41, some c124, some c40, some c123, some c11, some c42, some c99, some c98, some c52, some c19, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p139 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked139 : lratChecker f139 p139 = .success := by decide +kernel
theorem unsat139 : Unsatisfiable (PosFin 31) f139 := by
  apply lratCheckerSound f139 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p139
  · intro a ha; simp [p139] at ha; subst a; trivial
  · exact checked139
theorem derived139 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c139 := by
  apply localUnsat_implies_entails f139 [c105, c135, c110, c138, c8, c41, c124, c40, c123, c11, c42, c99, c98, c52, c19] c139 unsat139 (by rfl) a
  have h0 : Entails.eval a c105 := h 104 (by decide)
  have h1 : Entails.eval a c135 := derived135 a h
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c138 := derived138 a h
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c41 := h 40 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c42 := h 41 (by decide)
  have h11 : Entails.eval a c99 := h 98 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c52 := h 51 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c140 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f140 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c139, some c106, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p140 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked140 : lratChecker f140 p140 = .success := by decide +kernel
theorem unsat140 : Unsatisfiable (PosFin 31) f140 := by
  apply lratCheckerSound f140 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p140
  · intro a ha; simp [p140] at ha; subst a; trivial
  · exact checked140
theorem derived140 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c140 := by
  apply localUnsat_implies_entails f140 [c139, c106] c140 unsat140 (by rfl) a
  have h0 : Entails.eval a c139 := derived139 a h
  have h1 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c141 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨15, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f141 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c62, some c52, some c123, some c29, some c124, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p141 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked141 : lratChecker f141 p141 = .success := by decide +kernel
theorem unsat141 : Unsatisfiable (PosFin 31) f141 := by
  apply lratCheckerSound f141 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p141
  · intro a ha; simp [p141] at ha; subst a; trivial
  · exact checked141
theorem derived141 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c141 := by
  apply localUnsat_implies_entails f141 [c140, c62, c52, c123, c29, c124] c141 unsat141 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c123 := h 122 (by decide)
  have h4 : Entails.eval a c29 := h 28 (by decide)
  have h5 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c142 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨23, by decide⟩, true), (⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f142 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c33, some c123, some c52, some c14, some c61, some c122, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p142 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked142 : lratChecker f142 p142 = .success := by decide +kernel
theorem unsat142 : Unsatisfiable (PosFin 31) f142 := by
  apply lratCheckerSound f142 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p142
  · intro a ha; simp [p142] at ha; subst a; trivial
  · exact checked142
theorem derived142 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c142 := by
  apply localUnsat_implies_entails f142 [c140, c33, c123, c52, c14, c61, c122] c142 unsat142 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c123 := h 122 (by decide)
  have h3 : Entails.eval a c52 := h 51 (by decide)
  have h4 : Entails.eval a c14 := h 13 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c143 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f143 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c141, some c142, some c124, some c41, some c38, some c45, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p143 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked143 : lratChecker f143 p143 = .success := by decide +kernel
theorem unsat143 : Unsatisfiable (PosFin 31) f143 := by
  apply lratCheckerSound f143 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p143
  · intro a ha; simp [p143] at ha; subst a; trivial
  · exact checked143
theorem derived143 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c143 := by
  apply localUnsat_implies_entails f143 [c140, c141, c142, c124, c41, c38, c45] c143 unsat143 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c141 := derived141 a h
  have h2 : Entails.eval a c142 := derived142 a h
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c144 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f144 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c33, some c143, some c110, some c109, some c111, some c142, some c124, some c38, some c55, some c45, some c88, some c108, some c85, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p144 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked144 : lratChecker f144 p144 = .success := by decide +kernel
theorem unsat144 : Unsatisfiable (PosFin 31) f144 := by
  apply lratCheckerSound f144 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p144
  · intro a ha; simp [p144] at ha; subst a; trivial
  · exact checked144
theorem derived144 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c144 := by
  apply localUnsat_implies_entails f144 [c140, c33, c143, c110, c109, c111, c142, c124, c38, c55, c45, c88, c108, c85] c144 unsat144 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c143 := derived143 a h
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c109 := h 108 (by decide)
  have h5 : Entails.eval a c111 := h 110 (by decide)
  have h6 : Entails.eval a c142 := derived142 a h
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c108 := h 107 (by decide)
  have h13 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c145 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f145 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c109, some c119, some c55, some c36, some c53, some c80, some c76, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p145 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked145 : lratChecker f145 p145 = .success := by decide +kernel
theorem unsat145 : Unsatisfiable (PosFin 31) f145 := by
  apply lratCheckerSound f145 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p145
  · intro a ha; simp [p145] at ha; subst a; trivial
  · exact checked145
theorem derived145 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c145 := by
  apply localUnsat_implies_entails f145 [c140, c109, c119, c55, c36, c53, c80, c76] c145 unsat145 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c109 := h 108 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c146 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f146 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c144, some c120, some c119, some c110, some c145, some c124, some c121, some c126, some c90, some c22, some c117, some c125, some c112, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p146 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked146 : lratChecker f146 p146 = .success := by decide +kernel
theorem unsat146 : Unsatisfiable (PosFin 31) f146 := by
  apply lratCheckerSound f146 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p146
  · intro a ha; simp [p146] at ha; subst a; trivial
  · exact checked146
theorem derived146 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c146 := by
  apply localUnsat_implies_entails f146 [c144, c120, c119, c110, c145, c124, c121, c126, c90, c22, c117, c125, c112] c146 unsat146 (by rfl) a
  have h0 : Entails.eval a c144 := derived144 a h
  have h1 : Entails.eval a c120 := h 119 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c110 := h 109 (by decide)
  have h4 : Entails.eval a c145 := derived145 a h
  have h5 : Entails.eval a c124 := h 123 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c126 := derived126 a h
  have h8 : Entails.eval a c90 := h 89 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  have h10 : Entails.eval a c117 := h 116 (by decide)
  have h11 : Entails.eval a c125 := h 124 (by decide)
  have h12 : Entails.eval a c112 := h 111 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c147 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f147 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c144, some c124, some c40, some c90, some c45, some c60, some c74, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p147 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked147 : lratChecker f147 p147 = .success := by decide +kernel
theorem unsat147 : Unsatisfiable (PosFin 31) f147 := by
  apply lratCheckerSound f147 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p147
  · intro a ha; simp [p147] at ha; subst a; trivial
  · exact checked147
theorem derived147 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c147 := by
  apply localUnsat_implies_entails f147 [c140, c144, c124, c40, c90, c45, c60, c74] c147 unsat147 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c124 := h 123 (by decide)
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c60 := h 59 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c148 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f148 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c144, some c120, some c119, some c146, some c147, some c41, some c36, some c53, some c48, some c76, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p148 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked148 : lratChecker f148 p148 = .success := by decide +kernel
theorem unsat148 : Unsatisfiable (PosFin 31) f148 := by
  apply lratCheckerSound f148 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p148
  · intro a ha; simp [p148] at ha; subst a; trivial
  · exact checked148
theorem derived148 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c148 := by
  apply localUnsat_implies_entails f148 [c140, c144, c120, c119, c146, c147, c41, c36, c53, c48, c76] c148 unsat148 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c144 := derived144 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c146 := derived146 a h
  have h5 : Entails.eval a c147 := derived147 a h
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c149 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨27, by decide⟩, false), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f149 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c139, some c119, some c148, some c36, some c145, some c87, some c71, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p149 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked149 : lratChecker f149 p149 = .success := by decide +kernel
theorem unsat149 : Unsatisfiable (PosFin 31) f149 := by
  apply lratCheckerSound f149 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p149
  · intro a ha; simp [p149] at ha; subst a; trivial
  · exact checked149
theorem derived149 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c149 := by
  apply localUnsat_implies_entails f149 [c140, c139, c119, c148, c36, c145, c87, c71] c149 unsat149 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c139 := derived139 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c148 := derived148 a h
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c145 := derived145 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c150 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f150 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c148, some c120, some c149, some c40, some c104, some c17, some c48, some c100, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p150 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked150 : lratChecker f150 p150 = .success := by decide +kernel
theorem unsat150 : Unsatisfiable (PosFin 31) f150 := by
  apply lratCheckerSound f150 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p150
  · intro a ha; simp [p150] at ha; subst a; trivial
  · exact checked150
theorem derived150 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c150 := by
  apply localUnsat_implies_entails f150 [c140, c148, c120, c149, c40, c104, c17, c48, c100] c150 unsat150 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c148 := derived148 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c149 := derived149 a h
  have h4 : Entails.eval a c40 := h 39 (by decide)
  have h5 : Entails.eval a c104 := h 103 (by decide)
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c48 := h 47 (by decide)
  have h8 : Entails.eval a c100 := h 99 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c151 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f151 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c148, some c150, some c93, some c35, some c61, some c123, some c124, some c53, some c64, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p151 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked151 : lratChecker f151 p151 = .success := by decide +kernel
theorem unsat151 : Unsatisfiable (PosFin 31) f151 := by
  apply lratCheckerSound f151 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p151
  · intro a ha; simp [p151] at ha; subst a; trivial
  · exact checked151
theorem derived151 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c151 := by
  apply localUnsat_implies_entails f151 [c140, c148, c150, c93, c35, c61, c123, c124, c53, c64] c151 unsat151 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c148 := derived148 a h
  have h2 : Entails.eval a c150 := derived150 a h
  have h3 : Entails.eval a c93 := h 92 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c61 := h 60 (by decide)
  have h6 : Entails.eval a c123 := h 122 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c152 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f152 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c151, some c8, some c96, some c30, some c117, some c116, some c37, some c54, some c48, some c63, some c5, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p152 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked152 : lratChecker f152 p152 = .success := by decide +kernel
theorem unsat152 : Unsatisfiable (PosFin 31) f152 := by
  apply lratCheckerSound f152 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p152
  · intro a ha; simp [p152] at ha; subst a; trivial
  · exact checked152
theorem derived152 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c152 := by
  apply localUnsat_implies_entails f152 [c140, c151, c8, c96, c30, c117, c116, c37, c54, c48, c63, c5] c152 unsat152 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c151 := derived151 a h
  have h2 : Entails.eval a c8 := h 7 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  have h5 : Entails.eval a c117 := h 116 (by decide)
  have h6 : Entails.eval a c116 := h 115 (by decide)
  have h7 : Entails.eval a c37 := h 36 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  have h9 : Entails.eval a c48 := h 47 (by decide)
  have h10 : Entails.eval a c63 := h 62 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c153 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f153 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c151, some c152, some c120, some c94, some c145, some c95, some c110, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p153 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked153 : lratChecker f153 p153 = .success := by decide +kernel
theorem unsat153 : Unsatisfiable (PosFin 31) f153 := by
  apply lratCheckerSound f153 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p153
  · intro a ha; simp [p153] at ha; subst a; trivial
  · exact checked153
theorem derived153 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c153 := by
  apply localUnsat_implies_entails f153 [c151, c152, c120, c94, c145, c95, c110] c153 unsat153 (by rfl) a
  have h0 : Entails.eval a c151 := derived151 a h
  have h1 : Entails.eval a c152 := derived152 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c145 := derived145 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c154 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f154 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c153, some c140, some c139, some c120, some c27, some c91, some c63, some c12, some c15, some c57, some c118, some c1, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p154 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked154 : lratChecker f154 p154 = .success := by decide +kernel
theorem unsat154 : Unsatisfiable (PosFin 31) f154 := by
  apply lratCheckerSound f154 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p154
  · intro a ha; simp [p154] at ha; subst a; trivial
  · exact checked154
theorem derived154 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c154 := by
  apply localUnsat_implies_entails f154 [c153, c140, c139, c120, c27, c91, c63, c12, c15, c57, c118, c1] c154 unsat154 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c139 := derived139 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c27 := h 26 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c63 := h 62 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c57 := h 56 (by decide)
  have h10 : Entails.eval a c118 := h 117 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c155 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f155 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c153, some c140, some c120, some c119, some c75, some c154, some c17, some c36, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p155 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked155 : lratChecker f155 p155 = .success := by decide +kernel
theorem unsat155 : Unsatisfiable (PosFin 31) f155 := by
  apply lratCheckerSound f155 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p155
  · intro a ha; simp [p155] at ha; subst a; trivial
  · exact checked155
theorem derived155 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c155 := by
  apply localUnsat_implies_entails f155 [c153, c140, c120, c119, c75, c154, c17, c36] c155 unsat155 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c75 := h 74 (by decide)
  have h5 : Entails.eval a c154 := derived154 a h
  have h6 : Entails.eval a c17 := h 16 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c156 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f156 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c153, some c120, some c119, some c53, some c3, some c9, some c124, some c73, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p156 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked156 : lratChecker f156 p156 = .success := by decide +kernel
theorem unsat156 : Unsatisfiable (PosFin 31) f156 := by
  apply lratCheckerSound f156 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p156
  · intro a ha; simp [p156] at ha; subst a; trivial
  · exact checked156
theorem derived156 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c156 := by
  apply localUnsat_implies_entails f156 [c140, c153, c120, c119, c53, c3, c9, c124, c73] c156 unsat156 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c153 := derived153 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c53 := h 52 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c157 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f157 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c153, some c120, some c119, some c156, some c75, some c155, some c104, some c16, some c32, some c36, some c1, some c27, some (DefaultClause.unit (⟨15, by decide⟩, false))]
def p157 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked157 : lratChecker f157 p157 = .success := by decide +kernel
theorem unsat157 : Unsatisfiable (PosFin 31) f157 := by
  apply lratCheckerSound f157 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p157
  · intro a ha; simp [p157] at ha; subst a; trivial
  · exact checked157
theorem derived157 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c157 := by
  apply localUnsat_implies_entails f157 [c140, c153, c120, c119, c156, c75, c155, c104, c16, c32, c36, c1, c27] c157 unsat157 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c153 := derived153 a h
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c156 := derived156 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c155 := derived155 a h
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c16 := h 15 (by decide)
  have h9 : Entails.eval a c32 := h 31 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c1 := h 0 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c158 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f158 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c140, some c33, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p158 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked158 : lratChecker f158 p158 = .success := by decide +kernel
theorem unsat158 : Unsatisfiable (PosFin 31) f158 := by
  apply lratCheckerSound f158 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p158
  · intro a ha; simp [p158] at ha; subst a; trivial
  · exact checked158
theorem derived158 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c158 := by
  apply localUnsat_implies_entails f158 [c157, c140, c33] c158 unsat158 (by rfl) a
  have h0 : Entails.eval a c157 := derived157 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c159 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f159 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c157, some c140, some c153, some c158, some c16, some c1, some c26, some c35, some c104, some c64, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p159 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked159 : lratChecker f159 p159 = .success := by decide +kernel
theorem unsat159 : Unsatisfiable (PosFin 31) f159 := by
  apply lratCheckerSound f159 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p159
  · intro a ha; simp [p159] at ha; subst a; trivial
  · exact checked159
theorem derived159 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c159 := by
  apply localUnsat_implies_entails f159 [c157, c140, c153, c158, c16, c1, c26, c35, c104, c64] c159 unsat159 (by rfl) a
  have h0 : Entails.eval a c157 := derived157 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c153 := derived153 a h
  have h3 : Entails.eval a c158 := derived158 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c1 := h 0 (by decide)
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c160 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f160 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c153, some c157, some c140, some c46, some c61, some c93, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p160 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked160 : lratChecker f160 p160 = .success := by decide +kernel
theorem unsat160 : Unsatisfiable (PosFin 31) f160 := by
  apply lratCheckerSound f160 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p160
  · intro a ha; simp [p160] at ha; subst a; trivial
  · exact checked160
theorem derived160 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c160 := by
  apply localUnsat_implies_entails f160 [c153, c157, c140, c46, c61, c93] c160 unsat160 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c140 := derived140 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c61 := h 60 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c161 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f161 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c153, some c140, some c53, some c5, some c124, some c97, some c73, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p161 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked161 : lratChecker f161 p161 = .success := by decide +kernel
theorem unsat161 : Unsatisfiable (PosFin 31) f161 := by
  apply lratCheckerSound f161 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p161
  · intro a ha; simp [p161] at ha; subst a; trivial
  · exact checked161
theorem derived161 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c161 := by
  apply localUnsat_implies_entails f161 [c153, c140, c53, c5, c124, c97, c73] c161 unsat161 (by rfl) a
  have h0 : Entails.eval a c153 := derived153 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c124 := h 123 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c162 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f162 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c159, some c160, some c161, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p162 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked162 : lratChecker f162 p162 = .success := by decide +kernel
theorem unsat162 : Unsatisfiable (PosFin 31) f162 := by
  apply lratCheckerSound f162 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p162
  · intro a ha; simp [p162] at ha; subst a; trivial
  · exact checked162
theorem derived162 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c162 := by
  apply localUnsat_implies_entails f162 [c159, c160, c161] c162 unsat162 (by rfl) a
  have h0 : Entails.eval a c159 := derived159 a h
  have h1 : Entails.eval a c160 := derived160 a h
  have h2 : Entails.eval a c161 := derived161 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c163 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f163 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c140, some c157, some c153, some c162, some c158, some c123, some c35, some c52, some c26, some c92, some c1, some c13, some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p163 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked163 : lratChecker f163 p163 = .success := by decide +kernel
theorem unsat163 : Unsatisfiable (PosFin 31) f163 := by
  apply lratCheckerSound f163 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p163
  · intro a ha; simp [p163] at ha; subst a; trivial
  · exact checked163
theorem derived163 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c163 := by
  apply localUnsat_implies_entails f163 [c140, c157, c153, c162, c158, c123, c35, c52, c26, c92, c1, c13] c163 unsat163 (by rfl) a
  have h0 : Entails.eval a c140 := derived140 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c153 := derived153 a h
  have h3 : Entails.eval a c162 := derived162 a h
  have h4 : Entails.eval a c158 := derived158 a h
  have h5 : Entails.eval a c123 := h 122 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c92 := h 91 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c13 := h 12 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c164 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f164 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c163, some c124, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p164 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked164 : lratChecker f164 p164 = .success := by decide +kernel
theorem unsat164 : Unsatisfiable (PosFin 31) f164 := by
  apply lratCheckerSound f164 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p164
  · intro a ha; simp [p164] at ha; subst a; trivial
  · exact checked164
theorem derived164 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c164 := by
  apply localUnsat_implies_entails f164 [c163, c124] c164 unsat164 (by rfl) a
  have h0 : Entails.eval a c163 := derived163 a h
  have h1 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c165 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f165 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c158, some c157, some c140, some c164, some c153, some c27, some c49, some c1, some c35, some c52, some c13, some c55, some c101, some c47, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p165 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked165 : lratChecker f165 p165 = .success := by decide +kernel
theorem unsat165 : Unsatisfiable (PosFin 31) f165 := by
  apply lratCheckerSound f165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p165
  · intro a ha; simp [p165] at ha; subst a; trivial
  · exact checked165
theorem derived165 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c165 := by
  apply localUnsat_implies_entails f165 [c158, c157, c140, c164, c153, c27, c49, c1, c35, c52, c13, c55, c101, c47] c165 unsat165 (by rfl) a
  have h0 : Entails.eval a c158 := derived158 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c140 := derived140 a h
  have h3 : Entails.eval a c164 := derived164 a h
  have h4 : Entails.eval a c153 := derived153 a h
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c49 := h 48 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  have h10 : Entails.eval a c13 := h 12 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c101 := h 100 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c166 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f166 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c165, some c140, some c164, some c36, some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p166 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked166 : lratChecker f166 p166 = .success := by decide +kernel
theorem unsat166 : Unsatisfiable (PosFin 31) f166 := by
  apply lratCheckerSound f166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p166
  · intro a ha; simp [p166] at ha; subst a; trivial
  · exact checked166
theorem derived166 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c166 := by
  apply localUnsat_implies_entails f166 [c165, c140, c164, c36] c166 unsat166 (by rfl) a
  have h0 : Entails.eval a c165 := derived165 a h
  have h1 : Entails.eval a c140 := derived140 a h
  have h2 : Entails.eval a c164 := derived164 a h
  have h3 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c167 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f167 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c166, some c157, some c153, some c46, some (DefaultClause.unit (⟨8, by decide⟩, true))]
def p167 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked167 : lratChecker f167 p167 = .success := by decide +kernel
theorem unsat167 : Unsatisfiable (PosFin 31) f167 := by
  apply lratCheckerSound f167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p167
  · intro a ha; simp [p167] at ha; subst a; trivial
  · exact checked167
theorem derived167 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c167 := by
  apply localUnsat_implies_entails f167 [c166, c157, c153, c46] c167 unsat167 (by rfl) a
  have h0 : Entails.eval a c166 := derived166 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c153 := derived153 a h
  have h3 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c168 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f168 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c166, some c162, some c157, some c67, some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p168 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked168 : lratChecker f168 p168 = .success := by decide +kernel
theorem unsat168 : Unsatisfiable (PosFin 31) f168 := by
  apply lratCheckerSound f168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p168
  · intro a ha; simp [p168] at ha; subst a; trivial
  · exact checked168
theorem derived168 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c168 := by
  apply localUnsat_implies_entails f168 [c166, c162, c157, c67] c168 unsat168 (by rfl) a
  have h0 : Entails.eval a c166 := derived166 a h
  have h1 : Entails.eval a c162 := derived162 a h
  have h2 : Entails.eval a c157 := derived157 a h
  have h3 : Entails.eval a c67 := h 66 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c169 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f169 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c157, some c140, some c35, some (DefaultClause.unit (⟨20, by decide⟩, false))]
def p169 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked169 : lratChecker f169 p169 = .success := by decide +kernel
theorem unsat169 : Unsatisfiable (PosFin 31) f169 := by
  apply lratCheckerSound f169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p169
  · intro a ha; simp [p169] at ha; subst a; trivial
  · exact checked169
theorem derived169 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c169 := by
  apply localUnsat_implies_entails f169 [c167, c157, c140, c35] c169 unsat169 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c140 := derived140 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c170 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f170 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c157, some c166, some c66, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p170 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked170 : lratChecker f170 p170 = .success := by decide +kernel
theorem unsat170 : Unsatisfiable (PosFin 31) f170 := by
  apply lratCheckerSound f170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p170
  · intro a ha; simp [p170] at ha; subst a; trivial
  · exact checked170
theorem derived170 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c170 := by
  apply localUnsat_implies_entails f170 [c168, c157, c166, c66] c170 unsat170 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c157 := derived157 a h
  have h2 : Entails.eval a c166 := derived166 a h
  have h3 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c171 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f171 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c170, some c169, some c164, some c162, some c68]
def p171 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked171 : lratChecker f171 p171 = .success := by decide +kernel
theorem unsat171 : Unsatisfiable (PosFin 31) f171 := by
  apply lratCheckerSound f171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p171
  · intro a ha; simp [p171] at ha; subst a; trivial
  · exact checked171
theorem derived171 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c171 := by
  apply localUnsat_implies_entails f171 [c170, c169, c164, c162, c68] c171 unsat171 (by rfl) a
  have h0 : Entails.eval a c170 := derived170 a h
  have h1 : Entails.eval a c169 := derived169 a h
  have h2 : Entails.eval a c164 := derived164 a h
  have h3 : Entails.eval a c162 := derived162 a h
  have h4 : Entails.eval a c68 := h 67 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived171

end CochromaticTwenty.Certificates.Z12Direct_5_1_6
