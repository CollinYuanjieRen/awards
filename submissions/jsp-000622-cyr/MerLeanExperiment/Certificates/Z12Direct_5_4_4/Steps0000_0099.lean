import MerLeanExperiment.Certificates.Z12Direct_5_4_4.Inputs

/-! Generated from the actual pinned z12direct_5_4_4-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_4_4
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c200 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨18, by decide⟩, false), (⟨17, by decide⟩, true), (⟨16, by decide⟩, false), (⟨23, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c3, some c17, some c66, some c156, some c157, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked200 : lratChecker f200 p200 = .success := by decide +kernel
theorem unsat200 : Unsatisfiable (PosFin 31) f200 := by
  apply lratCheckerSound f200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p200
  · intro a ha; simp [p200] at ha; subst a; trivial
  · exact checked200
theorem derived200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c200 := by
  apply localUnsat_implies_entails f200 [c26, c3, c17, c66, c156, c157] c200 unsat200 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c66 := h 65 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c201 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c23, some c43, some c50, some c46, some c39, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked201 : lratChecker f201 p201 = .success := by decide +kernel
theorem unsat201 : Unsatisfiable (PosFin 31) f201 := by
  apply lratCheckerSound f201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p201
  · intro a ha; simp [p201] at ha; subst a; trivial
  · exact checked201
theorem derived201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c201 := by
  apply localUnsat_implies_entails f201 [c23, c43, c50, c46, c39] c201 unsat201 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c46 := h 45 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c202 : DefaultClause 31 := directClause [(⟨16, by decide⟩, false), (⟨27, by decide⟩, false), (⟨11, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c27, some c17, some c44, some c52, some c40, some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked202 : lratChecker f202 p202 = .success := by decide +kernel
theorem unsat202 : Unsatisfiable (PosFin 31) f202 := by
  apply lratCheckerSound f202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p202
  · intro a ha; simp [p202] at ha; subst a; trivial
  · exact checked202
theorem derived202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c202 := by
  apply localUnsat_implies_entails f202 [c26, c27, c17, c44, c52, c40] c202 unsat202 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c27 := h 26 (by decide)
  have h2 : Entails.eval a c17 := h 16 (by decide)
  have h3 : Entails.eval a c44 := h 43 (by decide)
  have h4 : Entails.eval a c52 := h 51 (by decide)
  have h5 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c203 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨16, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c41, some c201, some c96, some c82, some c94, some c89, some c6, some c115, some c7, some c66, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked203 : lratChecker f203 p203 = .success := by decide +kernel
theorem unsat203 : Unsatisfiable (PosFin 31) f203 := by
  apply lratCheckerSound f203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p203
  · intro a ha; simp [p203] at ha; subst a; trivial
  · exact checked203
theorem derived203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c203 := by
  apply localUnsat_implies_entails f203 [c41, c201, c96, c82, c94, c89, c6, c115, c7, c66] c203 unsat203 (by rfl) a
  have h0 : Entails.eval a c41 := h 40 (by decide)
  have h1 : Entails.eval a c201 := derived201 a h
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c94 := h 93 (by decide)
  have h5 : Entails.eval a c89 := h 88 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c7 := h 6 (by decide)
  have h9 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c204 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c28, some c43, some c51, some c47, some c39, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked204 : lratChecker f204 p204 = .success := by decide +kernel
theorem unsat204 : Unsatisfiable (PosFin 31) f204 := by
  apply lratCheckerSound f204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p204
  · intro a ha; simp [p204] at ha; subst a; trivial
  · exact checked204
theorem derived204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c204 := by
  apply localUnsat_implies_entails f204 [c28, c43, c51, c47, c39] c204 unsat204 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c205 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c201, some c204, some c3, some c94, some c89, some c79, some c78, some c96, some c104, some c115, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked205 : lratChecker f205 p205 = .success := by decide +kernel
theorem unsat205 : Unsatisfiable (PosFin 31) f205 := by
  apply lratCheckerSound f205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p205
  · intro a ha; simp [p205] at ha; subst a; trivial
  · exact checked205
theorem derived205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c205 := by
  apply localUnsat_implies_entails f205 [c201, c204, c3, c94, c89, c79, c78, c96, c104, c115] c205 unsat205 (by rfl) a
  have h0 : Entails.eval a c201 := derived201 a h
  have h1 : Entails.eval a c204 := derived204 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c79 := h 78 (by decide)
  have h6 : Entails.eval a c78 := h 77 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c104 := h 103 (by decide)
  have h9 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c206 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c203, some c205, some c82, some c77, some c96, some c116, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked206 : lratChecker f206 p206 = .success := by decide +kernel
theorem unsat206 : Unsatisfiable (PosFin 31) f206 := by
  apply lratCheckerSound f206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p206
  · intro a ha; simp [p206] at ha; subst a; trivial
  · exact checked206
theorem derived206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c206 := by
  apply localUnsat_implies_entails f206 [c203, c205, c82, c77, c96, c116] c206 unsat206 (by rfl) a
  have h0 : Entails.eval a c203 := derived203 a h
  have h1 : Entails.eval a c205 := derived205 a h
  have h2 : Entails.eval a c82 := h 81 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c207 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c201, some c204, some c3, some c206, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked207 : lratChecker f207 p207 = .success := by decide +kernel
theorem unsat207 : Unsatisfiable (PosFin 31) f207 := by
  apply lratCheckerSound f207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p207
  · intro a ha; simp [p207] at ha; subst a; trivial
  · exact checked207
theorem derived207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c207 := by
  apply localUnsat_implies_entails f207 [c201, c204, c3, c206] c207 unsat207 (by rfl) a
  have h0 : Entails.eval a c201 := derived201 a h
  have h1 : Entails.eval a c204 := derived204 a h
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c206 := derived206 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c208 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c207, some c37, some c145, some c179, some c117, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked208 : lratChecker f208 p208 = .success := by decide +kernel
theorem unsat208 : Unsatisfiable (PosFin 31) f208 := by
  apply lratCheckerSound f208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p208
  · intro a ha; simp [p208] at ha; subst a; trivial
  · exact checked208
theorem derived208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c208 := by
  apply localUnsat_implies_entails f208 [c207, c37, c145, c179, c117] c208 unsat208 (by rfl) a
  have h0 : Entails.eval a c207 := derived207 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c145 := h 144 (by decide)
  have h3 : Entails.eval a c179 := h 178 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c209 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c10, some c34, some c99, some c30, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked209 : lratChecker f209 p209 = .success := by decide +kernel
theorem unsat209 : Unsatisfiable (PosFin 31) f209 := by
  apply lratCheckerSound f209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p209
  · intro a ha; simp [p209] at ha; subst a; trivial
  · exact checked209
theorem derived209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c209 := by
  apply localUnsat_implies_entails f209 [c10, c34, c99, c30] c209 unsat209 (by rfl) a
  have h0 : Entails.eval a c10 := h 9 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c210 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c207, some c37, some c134, some c167, some c117, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked210 : lratChecker f210 p210 = .success := by decide +kernel
theorem unsat210 : Unsatisfiable (PosFin 31) f210 := by
  apply lratCheckerSound f210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p210
  · intro a ha; simp [p210] at ha; subst a; trivial
  · exact checked210
theorem derived210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c210 := by
  apply localUnsat_implies_entails f210 [c207, c37, c134, c167, c117] c210 unsat210 (by rfl) a
  have h0 : Entails.eval a c207 := derived207 a h
  have h1 : Entails.eval a c37 := h 36 (by decide)
  have h2 : Entails.eval a c134 := h 133 (by decide)
  have h3 : Entails.eval a c167 := h 166 (by decide)
  have h4 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c211 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c210, some c208, some c207, some c37, some c209, some c94, some c89, some c11, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked211 : lratChecker f211 p211 = .success := by decide +kernel
theorem unsat211 : Unsatisfiable (PosFin 31) f211 := by
  apply lratCheckerSound f211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p211
  · intro a ha; simp [p211] at ha; subst a; trivial
  · exact checked211
theorem derived211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c211 := by
  apply localUnsat_implies_entails f211 [c210, c208, c207, c37, c209, c94, c89, c11] c211 unsat211 (by rfl) a
  have h0 : Entails.eval a c210 := derived210 a h
  have h1 : Entails.eval a c208 := derived208 a h
  have h2 : Entails.eval a c207 := derived207 a h
  have h3 : Entails.eval a c37 := h 36 (by decide)
  have h4 : Entails.eval a c209 := derived209 a h
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c212 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c211, some c23, some c3, some c51, some c47, some c39, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked212 : lratChecker f212 p212 = .success := by decide +kernel
theorem unsat212 : Unsatisfiable (PosFin 31) f212 := by
  apply lratCheckerSound f212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p212
  · intro a ha; simp [p212] at ha; subst a; trivial
  · exact checked212
theorem derived212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c212 := by
  apply localUnsat_implies_entails f212 [c211, c23, c3, c51, c47, c39] c212 unsat212 (by rfl) a
  have h0 : Entails.eval a c211 := derived211 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c3 := h 2 (by decide)
  have h3 : Entails.eval a c51 := h 50 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c213 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨6, by decide⟩, false), (⟨24, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c68, some c71, some c59, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked213 : lratChecker f213 p213 = .success := by decide +kernel
theorem unsat213 : Unsatisfiable (PosFin 31) f213 := by
  apply lratCheckerSound f213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p213
  · intro a ha; simp [p213] at ha; subst a; trivial
  · exact checked213
theorem derived213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c213 := by
  apply localUnsat_implies_entails f213 [c68, c71, c59] c213 unsat213 (by rfl) a
  have h0 : Entails.eval a c68 := h 67 (by decide)
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c59 := h 58 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c214 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c37, some c207, some c208, some c210, some c34, some c30, some c211, some c212, some c99, some c213, some c3, some c90, some c106, some c78, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked214 : lratChecker f214 p214 = .success := by decide +kernel
theorem unsat214 : Unsatisfiable (PosFin 31) f214 := by
  apply lratCheckerSound f214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p214
  · intro a ha; simp [p214] at ha; subst a; trivial
  · exact checked214
theorem derived214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c214 := by
  apply localUnsat_implies_entails f214 [c37, c207, c208, c210, c34, c30, c211, c212, c99, c213, c3, c90, c106, c78] c214 unsat214 (by rfl) a
  have h0 : Entails.eval a c37 := h 36 (by decide)
  have h1 : Entails.eval a c207 := derived207 a h
  have h2 : Entails.eval a c208 := derived208 a h
  have h3 : Entails.eval a c210 := derived210 a h
  have h4 : Entails.eval a c34 := h 33 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c211 := derived211 a h
  have h7 : Entails.eval a c212 := derived212 a h
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c213 := derived213 a h
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c106 := h 105 (by decide)
  have h13 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c215 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨28, by decide⟩, true), (⟨1, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c139, some c134, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked215 : lratChecker f215 p215 = .success := by decide +kernel
theorem unsat215 : Unsatisfiable (PosFin 31) f215 := by
  apply lratCheckerSound f215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p215
  · intro a ha; simp [p215] at ha; subst a; trivial
  · exact checked215
theorem derived215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c215 := by
  apply localUnsat_implies_entails f215 [c139, c134] c215 unsat215 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c216 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c192, some c146, some c166, some c119, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked216 : lratChecker f216 p216 = .success := by decide +kernel
theorem unsat216 : Unsatisfiable (PosFin 31) f216 := by
  apply lratCheckerSound f216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p216
  · intro a ha; simp [p216] at ha; subst a; trivial
  · exact checked216
theorem derived216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c216 := by
  apply localUnsat_implies_entails f216 [c214, c192, c146, c166, c119] c216 unsat216 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c166 := h 165 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c217 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c139, some c171, some c215, some c121, some c119, some c38, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked217 : lratChecker f217 p217 = .success := by decide +kernel
theorem unsat217 : Unsatisfiable (PosFin 31) f217 := by
  apply lratCheckerSound f217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p217
  · intro a ha; simp [p217] at ha; subst a; trivial
  · exact checked217
theorem derived217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c217 := by
  apply localUnsat_implies_entails f217 [c139, c171, c215, c121, c119, c38] c217 unsat217 (by rfl) a
  have h0 : Entails.eval a c139 := h 138 (by decide)
  have h1 : Entails.eval a c171 := h 170 (by decide)
  have h2 : Entails.eval a c215 := derived215 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c218 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c86, some c192, some c19, some c119, some c186, some c143, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked218 : lratChecker f218 p218 = .success := by decide +kernel
theorem unsat218 : Unsatisfiable (PosFin 31) f218 := by
  apply lratCheckerSound f218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p218
  · intro a ha; simp [p218] at ha; subst a; trivial
  · exact checked218
theorem derived218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c218 := by
  apply localUnsat_implies_entails f218 [c86, c192, c19, c119, c186, c143] c218 unsat218 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c119 := h 118 (by decide)
  have h4 : Entails.eval a c186 := h 185 (by decide)
  have h5 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c219 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c62, some c86, some c218, some c35, some c184, some c20, some c155, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked219 : lratChecker f219 p219 = .success := by decide +kernel
theorem unsat219 : Unsatisfiable (PosFin 31) f219 := by
  apply lratCheckerSound f219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p219
  · intro a ha; simp [p219] at ha; subst a; trivial
  · exact checked219
theorem derived219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c219 := by
  apply localUnsat_implies_entails f219 [c62, c86, c218, c35, c184, c20, c155] c219 unsat219 (by rfl) a
  have h0 : Entails.eval a c62 := h 61 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c218 := derived218 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c184 := h 183 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c220 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c62, some c216, some c219, some c134, some c167, some c35, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked220 : lratChecker f220 p220 = .success := by decide +kernel
theorem unsat220 : Unsatisfiable (PosFin 31) f220 := by
  apply lratCheckerSound f220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p220
  · intro a ha; simp [p220] at ha; subst a; trivial
  · exact checked220
theorem derived220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c220 := by
  apply localUnsat_implies_entails f220 [c214, c62, c216, c219, c134, c167, c35] c220 unsat220 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c62 := h 61 (by decide)
  have h2 : Entails.eval a c216 := derived216 a h
  have h3 : Entails.eval a c219 := derived219 a h
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c221 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨1, by decide⟩, true), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c216, some c217, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked221 : lratChecker f221 p221 = .success := by decide +kernel
theorem unsat221 : Unsatisfiable (PosFin 31) f221 := by
  apply lratCheckerSound f221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p221
  · intro a ha; simp [p221] at ha; subst a; trivial
  · exact checked221
theorem derived221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c221 := by
  apply localUnsat_implies_entails f221 [c214, c216, c217] c221 unsat221 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c216 := derived216 a h
  have h2 : Entails.eval a c217 := derived217 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c222 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨22, by decide⟩, true), (⟨1, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c86, some c192, some c160, some c190, some c138, some c20, some c128, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked222 : lratChecker f222 p222 = .success := by decide +kernel
theorem unsat222 : Unsatisfiable (PosFin 31) f222 := by
  apply lratCheckerSound f222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p222
  · intro a ha; simp [p222] at ha; subst a; trivial
  · exact checked222
theorem derived222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c222 := by
  apply localUnsat_implies_entails f222 [c86, c192, c160, c190, c138, c20, c128] c222 unsat222 (by rfl) a
  have h0 : Entails.eval a c86 := h 85 (by decide)
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c190 := h 189 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c223 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨1, by decide⟩, true), (⟨29, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c135, some c119, some c193, some c142, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked223 : lratChecker f223 p223 = .success := by decide +kernel
theorem unsat223 : Unsatisfiable (PosFin 31) f223 := by
  apply lratCheckerSound f223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p223
  · intro a ha; simp [p223] at ha; subst a; trivial
  · exact checked223
theorem derived223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c223 := by
  apply localUnsat_implies_entails f223 [c222, c135, c119, c193, c142] c223 unsat223 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c135 := h 134 (by decide)
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c224 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c86, some c192, some c56, some c4, some c107, some c220, some c71, some c221, some c223, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked224 : lratChecker f224 p224 = .success := by decide +kernel
theorem unsat224 : Unsatisfiable (PosFin 31) f224 := by
  apply lratCheckerSound f224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p224
  · intro a ha; simp [p224] at ha; subst a; trivial
  · exact checked224
theorem derived224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c224 := by
  apply localUnsat_implies_entails f224 [c214, c86, c192, c56, c4, c107, c220, c71, c221, c223] c224 unsat224 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c107 := h 106 (by decide)
  have h6 : Entails.eval a c220 := derived220 a h
  have h7 : Entails.eval a c71 := h 70 (by decide)
  have h8 : Entails.eval a c221 := derived221 a h
  have h9 : Entails.eval a c223 := derived223 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c225 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨25, by decide⟩, true), (⟨11, by decide⟩, true), (⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c3, some c86, some c192, some c98, some c99, some c71, some c160, some c190, some c158, some c20, some c128, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked225 : lratChecker f225 p225 = .success := by decide +kernel
theorem unsat225 : Unsatisfiable (PosFin 31) f225 := by
  apply lratCheckerSound f225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p225
  · intro a ha; simp [p225] at ha; subst a; trivial
  · exact checked225
theorem derived225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c225 := by
  apply localUnsat_implies_entails f225 [c3, c86, c192, c98, c99, c71, c160, c190, c158, c20, c128] c225 unsat225 (by rfl) a
  have h0 : Entails.eval a c3 := h 2 (by decide)
  have h1 : Entails.eval a c86 := h 85 (by decide)
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c71 := h 70 (by decide)
  have h6 : Entails.eval a c160 := h 159 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c158 := h 157 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c226 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c192, some c224, some c80, some c3, some c225, some c213, some c25, some c4, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked226 : lratChecker f226 p226 = .success := by decide +kernel
theorem unsat226 : Unsatisfiable (PosFin 31) f226 := by
  apply lratCheckerSound f226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p226
  · intro a ha; simp [p226] at ha; subst a; trivial
  · exact checked226
theorem derived226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c226 := by
  apply localUnsat_implies_entails f226 [c214, c192, c224, c80, c3, c225, c213, c25, c4] c226 unsat226 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c224 := derived224 a h
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c225 := derived225 a h
  have h6 : Entails.eval a c213 := derived213 a h
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c227 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c192, some c34, some c25, some c64, some c142, some c176, some c122, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked227 : lratChecker f227 p227 = .success := by decide +kernel
theorem unsat227 : Unsatisfiable (PosFin 31) f227 := by
  apply lratCheckerSound f227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p227
  · intro a ha; simp [p227] at ha; subst a; trivial
  · exact checked227
theorem derived227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c227 := by
  apply localUnsat_implies_entails f227 [c192, c34, c25, c64, c142, c176, c122] c227 unsat227 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c25 := h 24 (by decide)
  have h3 : Entails.eval a c64 := h 63 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c228 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, true), (⟨6, by decide⟩, true), (⟨13, by decide⟩, true), (⟨16, by decide⟩, true), (⟨12, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c192, some c64, some c63, some c98, some c142, some c176, some c58, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked228 : lratChecker f228 p228 = .success := by decide +kernel
theorem unsat228 : Unsatisfiable (PosFin 31) f228 := by
  apply lratCheckerSound f228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p228
  · intro a ha; simp [p228] at ha; subst a; trivial
  · exact checked228
theorem derived228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c228 := by
  apply localUnsat_implies_entails f228 [c192, c64, c63, c98, c142, c176, c58] c228 unsat228 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c63 := h 62 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c176 := h 175 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c229 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c226, some c85, some c192, some c48, some c47, some c16, some c1, some c71, some c76, some c227, some c228, some c65, some c56, some c98, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked229 : lratChecker f229 p229 = .success := by decide +kernel
theorem unsat229 : Unsatisfiable (PosFin 31) f229 := by
  apply lratCheckerSound f229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p229
  · intro a ha; simp [p229] at ha; subst a; trivial
  · exact checked229
theorem derived229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c229 := by
  apply localUnsat_implies_entails f229 [c214, c226, c85, c192, c48, c47, c16, c1, c71, c76, c227, c228, c65, c56, c98] c229 unsat229 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c226 := derived226 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c47 := h 46 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c71 := h 70 (by decide)
  have h9 : Entails.eval a c76 := h 75 (by decide)
  have h10 : Entails.eval a c227 := derived227 a h
  have h11 : Entails.eval a c228 := derived228 a h
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c56 := h 55 (by decide)
  have h14 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c230 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c3, some c214, some c226, some c85, some c62, some c216, some c103, some c83, some c84, some c100, some c153, some c57, some c151, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked230 : lratChecker f230 p230 = .success := by decide +kernel
theorem unsat230 : Unsatisfiable (PosFin 31) f230 := by
  apply lratCheckerSound f230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p230
  · intro a ha; simp [p230] at ha; subst a; trivial
  · exact checked230
theorem derived230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c230 := by
  apply localUnsat_implies_entails f230 [c229, c3, c214, c226, c85, c62, c216, c103, c83, c84, c100, c153, c57, c151] c230 unsat230 (by rfl) a
  have h0 : Entails.eval a c229 := derived229 a h
  have h1 : Entails.eval a c3 := h 2 (by decide)
  have h2 : Entails.eval a c214 := derived214 a h
  have h3 : Entails.eval a c226 := derived226 a h
  have h4 : Entails.eval a c85 := h 84 (by decide)
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c216 := derived216 a h
  have h7 : Entails.eval a c103 := h 102 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c153 := h 152 (by decide)
  have h12 : Entails.eval a c57 := h 56 (by decide)
  have h13 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c231 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c84, some c61, some c57, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked231 : lratChecker f231 p231 = .success := by decide +kernel
theorem unsat231 : Unsatisfiable (PosFin 31) f231 := by
  apply lratCheckerSound f231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p231
  · intro a ha; simp [p231] at ha; subst a; trivial
  · exact checked231
theorem derived231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c231 := by
  apply localUnsat_implies_entails f231 [c84, c61, c57] c231 unsat231 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c232 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c192, some c226, some c229, some c3, some c230, some c34, some c231, some c103, some c142, some c176, some c122, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked232 : lratChecker f232 p232 = .success := by decide +kernel
theorem unsat232 : Unsatisfiable (PosFin 31) f232 := by
  apply lratCheckerSound f232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p232
  · intro a ha; simp [p232] at ha; subst a; trivial
  · exact checked232
theorem derived232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c232 := by
  apply localUnsat_implies_entails f232 [c214, c192, c226, c229, c3, c230, c34, c231, c103, c142, c176, c122] c232 unsat232 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c226 := derived226 a h
  have h3 : Entails.eval a c229 := derived229 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  have h5 : Entails.eval a c230 := derived230 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c231 := derived231 a h
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c176 := h 175 (by decide)
  have h11 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c233 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨24, by decide⟩, false), (⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c192, some c34, some c142, some c176, some c122, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked233 : lratChecker f233 p233 = .success := by decide +kernel
theorem unsat233 : Unsatisfiable (PosFin 31) f233 := by
  apply lratCheckerSound f233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p233
  · intro a ha; simp [p233] at ha; subst a; trivial
  · exact checked233
theorem derived233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c233 := by
  apply localUnsat_implies_entails f233 [c192, c34, c142, c176, c122] c233 unsat233 (by rfl) a
  have h0 : Entails.eval a c192 := h 191 (by decide)
  have h1 : Entails.eval a c34 := h 33 (by decide)
  have h2 : Entails.eval a c142 := h 141 (by decide)
  have h3 : Entails.eval a c176 := h 175 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c234 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c232, some c214, some c192, some c10, some c233, some c99, some c89, some c104, some c97, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked234 : lratChecker f234 p234 = .success := by decide +kernel
theorem unsat234 : Unsatisfiable (PosFin 31) f234 := by
  apply lratCheckerSound f234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p234
  · intro a ha; simp [p234] at ha; subst a; trivial
  · exact checked234
theorem derived234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c234 := by
  apply localUnsat_implies_entails f234 [c232, c214, c192, c10, c233, c99, c89, c104, c97] c234 unsat234 (by rfl) a
  have h0 : Entails.eval a c232 := derived232 a h
  have h1 : Entails.eval a c214 := derived214 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c233 := derived233 a h
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c97 := h 96 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c235 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c216, some c214, some c192, some c232, some c9, some c89, some c104, some c83, some c159, some c1, some c11, some c5, some c69, some c187, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked235 : lratChecker f235 p235 = .success := by decide +kernel
theorem unsat235 : Unsatisfiable (PosFin 31) f235 := by
  apply lratCheckerSound f235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p235
  · intro a ha; simp [p235] at ha; subst a; trivial
  · exact checked235
theorem derived235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c235 := by
  apply localUnsat_implies_entails f235 [c234, c216, c214, c192, c232, c9, c89, c104, c83, c159, c1, c11, c5, c69, c187] c235 unsat235 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c216 := derived216 a h
  have h2 : Entails.eval a c214 := derived214 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c232 := derived232 a h
  have h5 : Entails.eval a c9 := h 8 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  have h8 : Entails.eval a c83 := h 82 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c1 := h 0 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  have h12 : Entails.eval a c5 := h 4 (by decide)
  have h13 : Entails.eval a c69 := h 68 (by decide)
  have h14 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c236 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨17, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c232, some c214, some c192, some c9, some c216, some c235, some c105, some c99, some c111, some c96, some c11, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked236 : lratChecker f236 p236 = .success := by decide +kernel
theorem unsat236 : Unsatisfiable (PosFin 31) f236 := by
  apply lratCheckerSound f236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p236
  · intro a ha; simp [p236] at ha; subst a; trivial
  · exact checked236
theorem derived236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c236 := by
  apply localUnsat_implies_entails f236 [c234, c232, c214, c192, c9, c216, c235, c105, c99, c111, c96, c11] c236 unsat236 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c232 := derived232 a h
  have h2 : Entails.eval a c214 := derived214 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c216 := derived216 a h
  have h6 : Entails.eval a c235 := derived235 a h
  have h7 : Entails.eval a c105 := h 104 (by decide)
  have h8 : Entails.eval a c99 := h 98 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c11 := h 10 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c237 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c214, some c119, some c193, some c142, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked237 : lratChecker f237 p237 = .success := by decide +kernel
theorem unsat237 : Unsatisfiable (PosFin 31) f237 := by
  apply lratCheckerSound f237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p237
  · intro a ha; simp [p237] at ha; subst a; trivial
  · exact checked237
theorem derived237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c237 := by
  apply localUnsat_implies_entails f237 [c234, c214, c119, c193, c142] c237 unsat237 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c214 := derived214 a h
  have h2 : Entails.eval a c119 := h 118 (by decide)
  have h3 : Entails.eval a c193 := h 192 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c238 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c237, some c135, some c232, some c214, some c192, some c105, some c111, some c114, some c140, some c11, some c138, some c21, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked238 : lratChecker f238 p238 = .success := by decide +kernel
theorem unsat238 : Unsatisfiable (PosFin 31) f238 := by
  apply lratCheckerSound f238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p238
  · intro a ha; simp [p238] at ha; subst a; trivial
  · exact checked238
theorem derived238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c238 := by
  apply localUnsat_implies_entails f238 [c234, c237, c135, c232, c214, c192, c105, c111, c114, c140, c11, c138, c21] c238 unsat238 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c237 := derived237 a h
  have h2 : Entails.eval a c135 := h 134 (by decide)
  have h3 : Entails.eval a c232 := derived232 a h
  have h4 : Entails.eval a c214 := derived214 a h
  have h5 : Entails.eval a c192 := h 191 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  have h7 : Entails.eval a c111 := h 110 (by decide)
  have h8 : Entails.eval a c114 := h 113 (by decide)
  have h9 : Entails.eval a c140 := h 139 (by decide)
  have h10 : Entails.eval a c11 := h 10 (by decide)
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c239 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c234, some c232, some c214, some c192, some c237, some c135, some c238, some c94, some c89, some c104, some c5, some c136, some c11, some c138, some c21, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked239 : lratChecker f239 p239 = .success := by decide +kernel
theorem unsat239 : Unsatisfiable (PosFin 31) f239 := by
  apply lratCheckerSound f239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p239
  · intro a ha; simp [p239] at ha; subst a; trivial
  · exact checked239
theorem derived239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c239 := by
  apply localUnsat_implies_entails f239 [c234, c232, c214, c192, c237, c135, c238, c94, c89, c104, c5, c136, c11, c138, c21] c239 unsat239 (by rfl) a
  have h0 : Entails.eval a c234 := derived234 a h
  have h1 : Entails.eval a c232 := derived232 a h
  have h2 : Entails.eval a c214 := derived214 a h
  have h3 : Entails.eval a c192 := h 191 (by decide)
  have h4 : Entails.eval a c237 := derived237 a h
  have h5 : Entails.eval a c135 := h 134 (by decide)
  have h6 : Entails.eval a c238 := derived238 a h
  have h7 : Entails.eval a c94 := h 93 (by decide)
  have h8 : Entails.eval a c89 := h 88 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c5 := h 4 (by decide)
  have h11 : Entails.eval a c136 := h 135 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c138 := h 137 (by decide)
  have h14 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c240 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c192, some c232, some c239, some c9, some c236, some c76, some c24, some c15, some c67, some c6, some c29, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked240 : lratChecker f240 p240 = .success := by decide +kernel
theorem unsat240 : Unsatisfiable (PosFin 31) f240 := by
  apply lratCheckerSound f240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p240
  · intro a ha; simp [p240] at ha; subst a; trivial
  · exact checked240
theorem derived240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c240 := by
  apply localUnsat_implies_entails f240 [c214, c192, c232, c239, c9, c236, c76, c24, c15, c67, c6, c29] c240 unsat240 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  have h2 : Entails.eval a c232 := derived232 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c9 := h 8 (by decide)
  have h5 : Entails.eval a c236 := derived236 a h
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c67 := h 66 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c29 := h 28 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c241 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨5, by decide⟩, true), (⟨12, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c51, some c85, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked241 : lratChecker f241 p241 = .success := by decide +kernel
theorem unsat241 : Unsatisfiable (PosFin 31) f241 := by
  apply lratCheckerSound f241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p241
  · intro a ha; simp [p241] at ha; subst a; trivial
  · exact checked241
theorem derived241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c241 := by
  apply localUnsat_implies_entails f241 [c51, c85] c241 unsat241 (by rfl) a
  have h0 : Entails.eval a c51 := h 50 (by decide)
  have h1 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c242 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨5, by decide⟩, true), (⟨12, by decide⟩, false), (⟨23, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c241, some c83, some c147, some c81, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked242 : lratChecker f242 p242 = .success := by decide +kernel
theorem unsat242 : Unsatisfiable (PosFin 31) f242 := by
  apply lratCheckerSound f242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p242
  · intro a ha; simp [p242] at ha; subst a; trivial
  · exact checked242
theorem derived242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c242 := by
  apply localUnsat_implies_entails f242 [c240, c241, c83, c147, c81] c242 unsat242 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c241 := derived241 a h
  have h2 : Entails.eval a c83 := h 82 (by decide)
  have h3 : Entails.eval a c147 := h 146 (by decide)
  have h4 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c243 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨23, by decide⟩, false), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c76, some c64, some c65, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked243 : lratChecker f243 p243 = .success := by decide +kernel
theorem unsat243 : Unsatisfiable (PosFin 31) f243 := by
  apply lratCheckerSound f243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p243
  · intro a ha; simp [p243] at ha; subst a; trivial
  · exact checked243
theorem derived243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c243 := by
  apply localUnsat_implies_entails f243 [c76, c64, c65] c243 unsat243 (by rfl) a
  have h0 : Entails.eval a c76 := h 75 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c244 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨12, by decide⟩, true), (⟨1, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c215, some c217, some c43, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked244 : lratChecker f244 p244 = .success := by decide +kernel
theorem unsat244 : Unsatisfiable (PosFin 31) f244 := by
  apply lratCheckerSound f244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p244
  · intro a ha; simp [p244] at ha; subst a; trivial
  · exact checked244
theorem derived244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c244 := by
  apply localUnsat_implies_entails f244 [c215, c217, c43] c244 unsat244 (by rfl) a
  have h0 : Entails.eval a c215 := derived215 a h
  have h1 : Entails.eval a c217 := derived217 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c245 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨23, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c243, some c71, some c9, some c65, some c242, some c244, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked245 : lratChecker f245 p245 = .success := by decide +kernel
theorem unsat245 : Unsatisfiable (PosFin 31) f245 := by
  apply lratCheckerSound f245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p245
  · intro a ha; simp [p245] at ha; subst a; trivial
  · exact checked245
theorem derived245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c245 := by
  apply localUnsat_implies_entails f245 [c243, c71, c9, c65, c242, c244] c245 unsat245 (by rfl) a
  have h0 : Entails.eval a c243 := derived243 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c9 := h 8 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c242 := derived242 a h
  have h5 : Entails.eval a c244 := derived244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c246 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c24, some c243, some c71, some c245, some c2, some c11, some c6, some c190, some c96, some c55, some c242, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked246 : lratChecker f246 p246 = .success := by decide +kernel
theorem unsat246 : Unsatisfiable (PosFin 31) f246 := by
  apply lratCheckerSound f246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p246
  · intro a ha; simp [p246] at ha; subst a; trivial
  · exact checked246
theorem derived246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c246 := by
  apply localUnsat_implies_entails f246 [c24, c243, c71, c245, c2, c11, c6, c190, c96, c55, c242] c246 unsat246 (by rfl) a
  have h0 : Entails.eval a c24 := h 23 (by decide)
  have h1 : Entails.eval a c243 := derived243 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c245 := derived245 a h
  have h4 : Entails.eval a c2 := h 1 (by decide)
  have h5 : Entails.eval a c11 := h 10 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c190 := h 189 (by decide)
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c242 := derived242 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c247 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c134, some c120, some c38, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked247 : lratChecker f247 p247 = .success := by decide +kernel
theorem unsat247 : Unsatisfiable (PosFin 31) f247 := by
  apply lratCheckerSound f247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p247
  · intro a ha; simp [p247] at ha; subst a; trivial
  · exact checked247
theorem derived247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c247 := by
  apply localUnsat_implies_entails f247 [c240, c134, c120, c38] c247 unsat247 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c134 := h 133 (by decide)
  have h2 : Entails.eval a c120 := h 119 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c248 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c246, some c247, some c35, some c31, some c167, some c38, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked248 : lratChecker f248 p248 = .success := by decide +kernel
theorem unsat248 : Unsatisfiable (PosFin 31) f248 := by
  apply lratCheckerSound f248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p248
  · intro a ha; simp [p248] at ha; subst a; trivial
  · exact checked248
theorem derived248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c248 := by
  apply localUnsat_implies_entails f248 [c240, c246, c247, c35, c31, c167, c38] c248 unsat248 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c246 := derived246 a h
  have h2 : Entails.eval a c247 := derived247 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c249 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c248, some c32, some c35, some c118, some c167, some c119, some c24, some c243, some c71, some c148, some c170, some c51, some c45, some c244, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked249 : lratChecker f249 p249 = .success := by decide +kernel
theorem unsat249 : Unsatisfiable (PosFin 31) f249 := by
  apply lratCheckerSound f249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p249
  · intro a ha; simp [p249] at ha; subst a; trivial
  · exact checked249
theorem derived249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c249 := by
  apply localUnsat_implies_entails f249 [c240, c248, c32, c35, c118, c167, c119, c24, c243, c71, c148, c170, c51, c45, c244] c249 unsat249 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c248 := derived248 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c243 := derived243 a h
  have h9 : Entails.eval a c71 := h 70 (by decide)
  have h10 : Entails.eval a c148 := h 147 (by decide)
  have h11 : Entails.eval a c170 := h 169 (by decide)
  have h12 : Entails.eval a c51 := h 50 (by decide)
  have h13 : Entails.eval a c45 := h 44 (by decide)
  have h14 : Entails.eval a c244 := derived244 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c250 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c146, some c180, some c32, some c31, some c35, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked250 : lratChecker f250 p250 = .success := by decide +kernel
theorem unsat250 : Unsatisfiable (PosFin 31) f250 := by
  apply lratCheckerSound f250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p250
  · intro a ha; simp [p250] at ha; subst a; trivial
  · exact checked250
theorem derived250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c250 := by
  apply localUnsat_implies_entails f250 [c240, c146, c180, c32, c31, c35] c250 unsat250 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c146 := h 145 (by decide)
  have h2 : Entails.eval a c180 := h 179 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c35 := h 34 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c251 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c250, some c192, some c144, some c120, some c196, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked251 : lratChecker f251 p251 = .success := by decide +kernel
theorem unsat251 : Unsatisfiable (PosFin 31) f251 := by
  apply lratCheckerSound f251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p251
  · intro a ha; simp [p251] at ha; subst a; trivial
  · exact checked251
theorem derived251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c251 := by
  apply localUnsat_implies_entails f251 [c240, c250, c192, c144, c120, c196] c251 unsat251 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c250 := derived250 a h
  have h2 : Entails.eval a c192 := h 191 (by decide)
  have h3 : Entails.eval a c144 := h 143 (by decide)
  have h4 : Entails.eval a c120 := h 119 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c252 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨23, by decide⟩, true), (⟨25, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c32, some c247, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked252 : lratChecker f252 p252 = .success := by decide +kernel
theorem unsat252 : Unsatisfiable (PosFin 31) f252 := by
  apply lratCheckerSound f252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p252
  · intro a ha; simp [p252] at ha; subst a; trivial
  · exact checked252
theorem derived252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c252 := by
  apply localUnsat_implies_entails f252 [c240, c32, c247] c252 unsat252 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c247 := derived247 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c253 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c251, some c252, some c35, some c31, some c118, some c167, some c38, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked253 : lratChecker f253 p253 = .success := by decide +kernel
theorem unsat253 : Unsatisfiable (PosFin 31) f253 := by
  apply lratCheckerSound f253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p253
  · intro a ha; simp [p253] at ha; subst a; trivial
  · exact checked253
theorem derived253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c253 := by
  apply localUnsat_implies_entails f253 [c240, c251, c252, c35, c31, c118, c167, c38] c253 unsat253 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c251 := derived251 a h
  have h2 : Entails.eval a c252 := derived252 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c254 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c35, some c31, some c251, some c167, some c38, some c119, some c249, some c159, some c83, some c150, some c244, some c46, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked254 : lratChecker f254 p254 = .success := by decide +kernel
theorem unsat254 : Unsatisfiable (PosFin 31) f254 := by
  apply lratCheckerSound f254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p254
  · intro a ha; simp [p254] at ha; subst a; trivial
  · exact checked254
theorem derived254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c254 := by
  apply localUnsat_implies_entails f254 [c240, c35, c31, c251, c167, c38, c119, c249, c159, c83, c150, c244, c46] c254 unsat254 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c35 := h 34 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  have h3 : Entails.eval a c251 := derived251 a h
  have h4 : Entails.eval a c167 := h 166 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c119 := h 118 (by decide)
  have h7 : Entails.eval a c249 := derived249 a h
  have h8 : Entails.eval a c159 := h 158 (by decide)
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c150 := h 149 (by decide)
  have h11 : Entails.eval a c244 := derived244 a h
  have h12 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c255 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c254, some c35, some c31, some c251, some c167, some c38, some c119, some c253, some c249, some c99, some c111, some c90, some c3, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked255 : lratChecker f255 p255 = .success := by decide +kernel
theorem unsat255 : Unsatisfiable (PosFin 31) f255 := by
  apply lratCheckerSound f255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p255
  · intro a ha; simp [p255] at ha; subst a; trivial
  · exact checked255
theorem derived255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c255 := by
  apply localUnsat_implies_entails f255 [c240, c254, c35, c31, c251, c167, c38, c119, c253, c249, c99, c111, c90, c3] c255 unsat255 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c254 := derived254 a h
  have h2 : Entails.eval a c35 := h 34 (by decide)
  have h3 : Entails.eval a c31 := h 30 (by decide)
  have h4 : Entails.eval a c251 := derived251 a h
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c253 := derived253 a h
  have h9 : Entails.eval a c249 := derived249 a h
  have h10 : Entails.eval a c99 := h 98 (by decide)
  have h11 : Entails.eval a c111 := h 110 (by decide)
  have h12 : Entails.eval a c90 := h 89 (by decide)
  have h13 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c256 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c255, some c254, some c35, some c31, some c251, some c167, some c38, some c253, some c177, some c249, some c3, some c127, some c9, some c104, some c15, some c130, some c174, some c60, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked256 : lratChecker f256 p256 = .success := by decide +kernel
theorem unsat256 : Unsatisfiable (PosFin 31) f256 := by
  apply lratCheckerSound f256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p256
  · intro a ha; simp [p256] at ha; subst a; trivial
  · exact checked256
theorem derived256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c256 := by
  apply localUnsat_implies_entails f256 [c240, c255, c254, c35, c31, c251, c167, c38, c253, c177, c249, c3, c127, c9, c104, c15, c130, c174, c60] c256 unsat256 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c254 := derived254 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c251 := derived251 a h
  have h6 : Entails.eval a c167 := h 166 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c253 := derived253 a h
  have h9 : Entails.eval a c177 := h 176 (by decide)
  have h10 : Entails.eval a c249 := derived249 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c127 := h 126 (by decide)
  have h13 : Entails.eval a c9 := h 8 (by decide)
  have h14 : Entails.eval a c104 := h 103 (by decide)
  have h15 : Entails.eval a c15 := h 14 (by decide)
  have h16 : Entails.eval a c130 := h 129 (by decide)
  have h17 : Entails.eval a c174 := h 173 (by decide)
  have h18 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c257 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c253, some c251, some c35, some c31, some c167, some c177, some c38, some c119, some c254, some c255, some c256, some c22, some c108, some c57, some c90, some c172, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked257 : lratChecker f257 p257 = .success := by decide +kernel
theorem unsat257 : Unsatisfiable (PosFin 31) f257 := by
  apply lratCheckerSound f257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p257
  · intro a ha; simp [p257] at ha; subst a; trivial
  · exact checked257
theorem derived257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c257 := by
  apply localUnsat_implies_entails f257 [c240, c253, c251, c35, c31, c167, c177, c38, c119, c254, c255, c256, c22, c108, c57, c90, c172] c257 unsat257 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c253 := derived253 a h
  have h2 : Entails.eval a c251 := derived251 a h
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c31 := h 30 (by decide)
  have h5 : Entails.eval a c167 := h 166 (by decide)
  have h6 : Entails.eval a c177 := h 176 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c119 := h 118 (by decide)
  have h9 : Entails.eval a c254 := derived254 a h
  have h10 : Entails.eval a c255 := derived255 a h
  have h11 : Entails.eval a c256 := derived256 a h
  have h12 : Entails.eval a c22 := h 21 (by decide)
  have h13 : Entails.eval a c108 := h 107 (by decide)
  have h14 : Entails.eval a c57 := h 56 (by decide)
  have h15 : Entails.eval a c90 := h 89 (by decide)
  have h16 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c258 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨12, by decide⟩, false), (⟨1, by decide⟩, false), (⟨29, by decide⟩, false), (⟨19, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c22, some c88, some c57, some c90, some c172, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked258 : lratChecker f258 p258 = .success := by decide +kernel
theorem unsat258 : Unsatisfiable (PosFin 31) f258 := by
  apply lratCheckerSound f258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p258
  · intro a ha; simp [p258] at ha; subst a; trivial
  · exact checked258
theorem derived258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c258 := by
  apply localUnsat_implies_entails f258 [c22, c88, c57, c90, c172] c258 unsat258 (by rfl) a
  have h0 : Entails.eval a c22 := h 21 (by decide)
  have h1 : Entails.eval a c88 := h 87 (by decide)
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c90 := h 89 (by decide)
  have h4 : Entails.eval a c172 := h 171 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c259 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c257, some c251, some c134, some c32, some c38, some c121, some c31, some c253, some c143, some c249, some c3, some c202, some c126, some c9, some c2, some c152, some c101, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked259 : lratChecker f259 p259 = .success := by decide +kernel
theorem unsat259 : Unsatisfiable (PosFin 31) f259 := by
  apply lratCheckerSound f259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p259
  · intro a ha; simp [p259] at ha; subst a; trivial
  · exact checked259
theorem derived259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c259 := by
  apply localUnsat_implies_entails f259 [c240, c257, c251, c134, c32, c38, c121, c31, c253, c143, c249, c3, c202, c126, c9, c2, c152, c101] c259 unsat259 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c257 := derived257 a h
  have h2 : Entails.eval a c251 := derived251 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c32 := h 31 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c121 := h 120 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c253 := derived253 a h
  have h9 : Entails.eval a c143 := h 142 (by decide)
  have h10 : Entails.eval a c249 := derived249 a h
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c202 := derived202 a h
  have h13 : Entails.eval a c126 := h 125 (by decide)
  have h14 : Entails.eval a c9 := h 8 (by decide)
  have h15 : Entails.eval a c2 := h 1 (by decide)
  have h16 : Entails.eval a c152 := h 151 (by decide)
  have h17 : Entails.eval a c101 := h 100 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c260 : DefaultClause 31 := directClause [(⟨1, by decide⟩, false), (⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨23, by decide⟩, false), (⟨25, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c143, some c90, some c258, some c99, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked260 : lratChecker f260 p260 = .success := by decide +kernel
theorem unsat260 : Unsatisfiable (PosFin 31) f260 := by
  apply lratCheckerSound f260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p260
  · intro a ha; simp [p260] at ha; subst a; trivial
  · exact checked260
theorem derived260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c260 := by
  apply localUnsat_implies_entails f260 [c143, c90, c258, c99] c260 unsat260 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c90 := h 89 (by decide)
  have h2 : Entails.eval a c258 := derived258 a h
  have h3 : Entails.eval a c99 := h 98 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c261 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c251, some c253, some c257, some c134, some c32, some c38, some c31, some c121, some c259, some c260, some c83, some c182, some c244, some c46, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked261 : lratChecker f261 p261 = .success := by decide +kernel
theorem unsat261 : Unsatisfiable (PosFin 31) f261 := by
  apply lratCheckerSound f261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p261
  · intro a ha; simp [p261] at ha; subst a; trivial
  · exact checked261
theorem derived261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c261 := by
  apply localUnsat_implies_entails f261 [c240, c251, c253, c257, c134, c32, c38, c31, c121, c259, c260, c83, c182, c244, c46] c261 unsat261 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c251 := derived251 a h
  have h2 : Entails.eval a c253 := derived253 a h
  have h3 : Entails.eval a c257 := derived257 a h
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c32 := h 31 (by decide)
  have h6 : Entails.eval a c38 := h 37 (by decide)
  have h7 : Entails.eval a c31 := h 30 (by decide)
  have h8 : Entails.eval a c121 := h 120 (by decide)
  have h9 : Entails.eval a c259 := derived259 a h
  have h10 : Entails.eval a c260 := derived260 a h
  have h11 : Entails.eval a c83 := h 82 (by decide)
  have h12 : Entails.eval a c182 := h 181 (by decide)
  have h13 : Entails.eval a c244 := derived244 a h
  have h14 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c262 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c261, some c33, some c32, some c135, some c38, some c252, some c165, some c143, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked262 : lratChecker f262 p262 = .success := by decide +kernel
theorem unsat262 : Unsatisfiable (PosFin 31) f262 := by
  apply lratCheckerSound f262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p262
  · intro a ha; simp [p262] at ha; subst a; trivial
  · exact checked262
theorem derived262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c262 := by
  apply localUnsat_implies_entails f262 [c240, c261, c33, c32, c135, c38, c252, c165, c143] c262 unsat262 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c32 := h 31 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c252 := derived252 a h
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c143 := h 142 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c263 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c261, some c33, some c38, some c143, some c165, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked263 : lratChecker f263 p263 = .success := by decide +kernel
theorem unsat263 : Unsatisfiable (PosFin 31) f263 := by
  apply lratCheckerSound f263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p263
  · intro a ha; simp [p263] at ha; subst a; trivial
  · exact checked263
theorem derived263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c263 := by
  apply localUnsat_implies_entails f263 [c240, c261, c33, c38, c143, c165] c263 unsat263 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c38 := h 37 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c264 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c262, some c261, some c33, some c263, some c132, some c141, some c177, some c194, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked264 : lratChecker f264 p264 = .success := by decide +kernel
theorem unsat264 : Unsatisfiable (PosFin 31) f264 := by
  apply lratCheckerSound f264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p264
  · intro a ha; simp [p264] at ha; subst a; trivial
  · exact checked264
theorem derived264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c264 := by
  apply localUnsat_implies_entails f264 [c240, c262, c261, c33, c263, c132, c141, c177, c194] c264 unsat264 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c262 := derived262 a h
  have h2 : Entails.eval a c261 := derived261 a h
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c263 := derived263 a h
  have h5 : Entails.eval a c132 := h 131 (by decide)
  have h6 : Entails.eval a c141 := h 140 (by decide)
  have h7 : Entails.eval a c177 := h 176 (by decide)
  have h8 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c265 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c33, some c262, some c264, some c192, some c141, some c132, some c165, some c38, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked265 : lratChecker f265 p265 = .success := by decide +kernel
theorem unsat265 : Unsatisfiable (PosFin 31) f265 := by
  apply lratCheckerSound f265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p265
  · intro a ha; simp [p265] at ha; subst a; trivial
  · exact checked265
theorem derived265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c265 := by
  apply localUnsat_implies_entails f265 [c240, c33, c262, c264, c192, c141, c132, c165, c38] c265 unsat265 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c262 := derived262 a h
  have h3 : Entails.eval a c264 := derived264 a h
  have h4 : Entails.eval a c192 := h 191 (by decide)
  have h5 : Entails.eval a c141 := h 140 (by decide)
  have h6 : Entails.eval a c132 := h 131 (by decide)
  have h7 : Entails.eval a c165 := h 164 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c266 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c261, some c265, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked266 : lratChecker f266 p266 = .success := by decide +kernel
theorem unsat266 : Unsatisfiable (PosFin 31) f266 := by
  apply lratCheckerSound f266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p266
  · intro a ha; simp [p266] at ha; subst a; trivial
  · exact checked266
theorem derived266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c266 := by
  apply localUnsat_implies_entails f266 [c261, c265] c266 unsat266 (by rfl) a
  have h0 : Entails.eval a c261 := derived261 a h
  have h1 : Entails.eval a c265 := derived265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c267 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c36, some c38, some c30, some c145, some c131, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked267 : lratChecker f267 p267 = .success := by decide +kernel
theorem unsat267 : Unsatisfiable (PosFin 31) f267 := by
  apply lratCheckerSound f267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p267
  · intro a ha; simp [p267] at ha; subst a; trivial
  · exact checked267
theorem derived267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c267 := by
  apply localUnsat_implies_entails f267 [c240, c36, c38, c30, c145, c131] c267 unsat267 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c38 := h 37 (by decide)
  have h3 : Entails.eval a c30 := h 29 (by decide)
  have h4 : Entails.eval a c145 := h 144 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c268 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c240, some c267, some c120, some c165, some c131, some c133, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked268 : lratChecker f268 p268 = .success := by decide +kernel
theorem unsat268 : Unsatisfiable (PosFin 31) f268 := by
  apply lratCheckerSound f268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p268
  · intro a ha; simp [p268] at ha; subst a; trivial
  · exact checked268
theorem derived268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c268 := by
  apply localUnsat_implies_entails f268 [c266, c240, c267, c120, c165, c131, c133] c268 unsat268 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c267 := derived267 a h
  have h3 : Entails.eval a c120 := h 119 (by decide)
  have h4 : Entails.eval a c165 := h 164 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  have h6 : Entails.eval a c133 := h 132 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c269 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c240, some c233, some c268, some c132, some c118, some c164, some c175, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked269 : lratChecker f269 p269 = .success := by decide +kernel
theorem unsat269 : Unsatisfiable (PosFin 31) f269 := by
  apply lratCheckerSound f269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p269
  · intro a ha; simp [p269] at ha; subst a; trivial
  · exact checked269
theorem derived269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c269 := by
  apply localUnsat_implies_entails f269 [c266, c240, c233, c268, c132, c118, c164, c175] c269 unsat269 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c233 := derived233 a h
  have h3 : Entails.eval a c268 := derived268 a h
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c164 := h 163 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c270 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c266, some c269, some c34, some c132, some c165, some c122, some (DefaultClause.unit (⟨22, by decide⟩, false))]
def p270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked270 : lratChecker f270 p270 = .success := by decide +kernel
theorem unsat270 : Unsatisfiable (PosFin 31) f270 := by
  apply lratCheckerSound f270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p270
  · intro a ha; simp [p270] at ha; subst a; trivial
  · exact checked270
theorem derived270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c270 := by
  apply localUnsat_implies_entails f270 [c240, c266, c269, c34, c132, c165, c122] c270 unsat270 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c266 := derived266 a h
  have h2 : Entails.eval a c269 := derived269 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c165 := h 164 (by decide)
  have h6 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c271 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨7, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c10, some c106, some c213, some c3, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked271 : lratChecker f271 p271 = .success := by decide +kernel
theorem unsat271 : Unsatisfiable (PosFin 31) f271 := by
  apply lratCheckerSound f271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p271
  · intro a ha; simp [p271] at ha; subst a; trivial
  · exact checked271
theorem derived271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c271 := by
  apply localUnsat_implies_entails f271 [c266, c10, c106, c213, c3] c271 unsat271 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c10 := h 9 (by decide)
  have h2 : Entails.eval a c106 := h 105 (by decide)
  have h3 : Entails.eval a c213 := derived213 a h
  have h4 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c272 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c270, some c243, some c213, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked272 : lratChecker f272 p272 = .success := by decide +kernel
theorem unsat272 : Unsatisfiable (PosFin 31) f272 := by
  apply lratCheckerSound f272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p272
  · intro a ha; simp [p272] at ha; subst a; trivial
  · exact checked272
theorem derived272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c272 := by
  apply localUnsat_implies_entails f272 [c266, c270, c243, c213] c272 unsat272 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c270 := derived270 a h
  have h2 : Entails.eval a c243 := derived243 a h
  have h3 : Entails.eval a c213 := derived213 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c273 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f273 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c272, some c34, some c10, some c271, some c153, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p273 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked273 : lratChecker f273 p273 = .success := by decide +kernel
theorem unsat273 : Unsatisfiable (PosFin 31) f273 := by
  apply lratCheckerSound f273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p273
  · intro a ha; simp [p273] at ha; subst a; trivial
  · exact checked273
theorem derived273 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c273 := by
  apply localUnsat_implies_entails f273 [c266, c272, c34, c10, c271, c153] c273 unsat273 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c272 := derived272 a h
  have h2 : Entails.eval a c34 := h 33 (by decide)
  have h3 : Entails.eval a c10 := h 9 (by decide)
  have h4 : Entails.eval a c271 := derived271 a h
  have h5 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c274 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c240, some c266, some c122, some c273, some c12, some c64, some c146, some c272, some c34, some c200, some c191, some c61, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked274 : lratChecker f274 p274 = .success := by decide +kernel
theorem unsat274 : Unsatisfiable (PosFin 31) f274 := by
  apply lratCheckerSound f274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p274
  · intro a ha; simp [p274] at ha; subst a; trivial
  · exact checked274
theorem derived274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c274 := by
  apply localUnsat_implies_entails f274 [c270, c240, c266, c122, c273, c12, c64, c146, c272, c34, c200, c191, c61] c274 unsat274 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c273 := derived273 a h
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c146 := h 145 (by decide)
  have h8 : Entails.eval a c272 := derived272 a h
  have h9 : Entails.eval a c34 := h 33 (by decide)
  have h10 : Entails.eval a c200 := derived200 a h
  have h11 : Entails.eval a c191 := h 190 (by decide)
  have h12 : Entails.eval a c61 := h 60 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c275 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨27, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c270, some c240, some c146, some c122, some c273, some c99, some c12, some c274, some c83, some c88, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked275 : lratChecker f275 p275 = .success := by decide +kernel
theorem unsat275 : Unsatisfiable (PosFin 31) f275 := by
  apply lratCheckerSound f275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p275
  · intro a ha; simp [p275] at ha; subst a; trivial
  · exact checked275
theorem derived275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c275 := by
  apply localUnsat_implies_entails f275 [c266, c270, c240, c146, c122, c273, c99, c12, c274, c83, c88] c275 unsat275 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c270 := derived270 a h
  have h2 : Entails.eval a c240 := derived240 a h
  have h3 : Entails.eval a c146 := h 145 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c273 := derived273 a h
  have h6 : Entails.eval a c99 := h 98 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c274 := derived274 a h
  have h9 : Entails.eval a c83 := h 82 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c276 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨28, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c270, some c272, some c42, some c99, some c14, some c103, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked276 : lratChecker f276 p276 = .success := by decide +kernel
theorem unsat276 : Unsatisfiable (PosFin 31) f276 := by
  apply lratCheckerSound f276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p276
  · intro a ha; simp [p276] at ha; subst a; trivial
  · exact checked276
theorem derived276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c276 := by
  apply localUnsat_implies_entails f276 [c240, c270, c272, c42, c99, c14, c103] c276 unsat276 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c270 := derived270 a h
  have h2 : Entails.eval a c272 := derived272 a h
  have h3 : Entails.eval a c42 := h 41 (by decide)
  have h4 : Entails.eval a c99 := h 98 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c277 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c240, some c272, some c122, some c275, some c42, some c276, some c271, some c107, some c137, some c49, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked277 : lratChecker f277 p277 = .success := by decide +kernel
theorem unsat277 : Unsatisfiable (PosFin 31) f277 := by
  apply lratCheckerSound f277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p277
  · intro a ha; simp [p277] at ha; subst a; trivial
  · exact checked277
theorem derived277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c277 := by
  apply localUnsat_implies_entails f277 [c266, c240, c272, c122, c275, c42, c276, c271, c107, c137, c49] c277 unsat277 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c272 := derived272 a h
  have h3 : Entails.eval a c122 := h 121 (by decide)
  have h4 : Entails.eval a c275 := derived275 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c276 := derived276 a h
  have h7 : Entails.eval a c271 := derived271 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c137 := h 136 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c278 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c240, some c270, some c277, some c272, some c42, some c276, some c10, some c271, some c107, some c154, some c97, some c92, some c90, some c108, some c87, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked278 : lratChecker f278 p278 = .success := by decide +kernel
theorem unsat278 : Unsatisfiable (PosFin 31) f278 := by
  apply lratCheckerSound f278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p278
  · intro a ha; simp [p278] at ha; subst a; trivial
  · exact checked278
theorem derived278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c278 := by
  apply localUnsat_implies_entails f278 [c266, c240, c270, c277, c272, c42, c276, c10, c271, c107, c154, c97, c92, c90, c108, c87] c278 unsat278 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c272 := derived272 a h
  have h5 : Entails.eval a c42 := h 41 (by decide)
  have h6 : Entails.eval a c276 := derived276 a h
  have h7 : Entails.eval a c10 := h 9 (by decide)
  have h8 : Entails.eval a c271 := derived271 a h
  have h9 : Entails.eval a c107 := h 106 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c92 := h 91 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c108 := h 107 (by decide)
  have h15 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c279 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f279 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c240, some c278, some c277, some c272, some c34, some c10, some c271, some c107, some c183, some c92, some c113, some c93, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p279 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked279 : lratChecker f279 p279 = .success := by decide +kernel
theorem unsat279 : Unsatisfiable (PosFin 31) f279 := by
  apply lratCheckerSound f279 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p279
  · intro a ha; simp [p279] at ha; subst a; trivial
  · exact checked279
theorem derived279 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c279 := by
  apply localUnsat_implies_entails f279 [c266, c240, c278, c277, c272, c34, c10, c271, c107, c183, c92, c113, c93] c279 unsat279 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c278 := derived278 a h
  have h3 : Entails.eval a c277 := derived277 a h
  have h4 : Entails.eval a c272 := derived272 a h
  have h5 : Entails.eval a c34 := h 33 (by decide)
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c271 := derived271 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c183 := h 182 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c280 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f280 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c266, some c231, some c103, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p280 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked280 : lratChecker f280 p280 = .success := by decide +kernel
theorem unsat280 : Unsatisfiable (PosFin 31) f280 := by
  apply lratCheckerSound f280 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p280
  · intro a ha; simp [p280] at ha; subst a; trivial
  · exact checked280
theorem derived280 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c280 := by
  apply localUnsat_implies_entails f280 [c270, c266, c231, c103] c280 unsat280 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c266 := derived266 a h
  have h2 : Entails.eval a c231 := derived231 a h
  have h3 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c281 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f281 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c279, some c99, some c280, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p281 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked281 : lratChecker f281 p281 = .success := by decide +kernel
theorem unsat281 : Unsatisfiable (PosFin 31) f281 := by
  apply lratCheckerSound f281 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p281
  · intro a ha; simp [p281] at ha; subst a; trivial
  · exact checked281
theorem derived281 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c281 := by
  apply localUnsat_implies_entails f281 [c270, c279, c99, c280] c281 unsat281 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c279 := derived279 a h
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c280 := derived280 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c282 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f282 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c240, some c270, some c34, some c272, some c277, some c278, some c281, some c3, some c9, some c10, some c61, some c13, some c99, some c72, some c104, some c173, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p282 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked282 : lratChecker f282 p282 = .success := by decide +kernel
theorem unsat282 : Unsatisfiable (PosFin 31) f282 := by
  apply lratCheckerSound f282 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p282
  · intro a ha; simp [p282] at ha; subst a; trivial
  · exact checked282
theorem derived282 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c282 := by
  apply localUnsat_implies_entails f282 [c266, c240, c270, c34, c272, c277, c278, c281, c3, c9, c10, c61, c13, c99, c72, c104, c173] c282 unsat282 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c272 := derived272 a h
  have h5 : Entails.eval a c277 := derived277 a h
  have h6 : Entails.eval a c278 := derived278 a h
  have h7 : Entails.eval a c281 := derived281 a h
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c9 := h 8 (by decide)
  have h10 : Entails.eval a c10 := h 9 (by decide)
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c13 := h 12 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c72 := h 71 (by decide)
  have h15 : Entails.eval a c104 := h 103 (by decide)
  have h16 : Entails.eval a c173 := h 172 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c283 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f283 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c192, some (DefaultClause.unit (⟨29, by decide⟩, false))]
def p283 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked283 : lratChecker f283 p283 = .success := by decide +kernel
theorem unsat283 : Unsatisfiable (PosFin 31) f283 := by
  apply lratCheckerSound f283 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p283
  · intro a ha; simp [p283] at ha; subst a; trivial
  · exact checked283
theorem derived283 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c283 := by
  apply localUnsat_implies_entails f283 [c282, c192] c283 unsat283 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c284 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f284 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c240, some c282, some c115, some c118, some c13, some c8, some c74, some c123, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p284 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked284 : lratChecker f284 p284 = .success := by decide +kernel
theorem unsat284 : Unsatisfiable (PosFin 31) f284 := by
  apply lratCheckerSound f284 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p284
  · intro a ha; simp [p284] at ha; subst a; trivial
  · exact checked284
theorem derived284 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c284 := by
  apply localUnsat_implies_entails f284 [c270, c240, c282, c115, c118, c13, c8, c74, c123] c284 unsat284 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c282 := derived282 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c8 := h 7 (by decide)
  have h7 : Entails.eval a c74 := h 73 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c285 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨6, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f285 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c240, some c270, some c284, some c115, some c38, some c124, some c42, some c65, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p285 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked285 : lratChecker f285 p285 = .success := by decide +kernel
theorem unsat285 : Unsatisfiable (PosFin 31) f285 := by
  apply lratCheckerSound f285 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p285
  · intro a ha; simp [p285] at ha; subst a; trivial
  · exact checked285
theorem derived285 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c285 := by
  apply localUnsat_implies_entails f285 [c282, c240, c270, c284, c115, c38, c124, c42, c65] c285 unsat285 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c284 := derived284 a h
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c124 := h 123 (by decide)
  have h7 : Entails.eval a c42 := h 41 (by decide)
  have h8 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c286 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f286 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c282, some c270, some c115, some c284, some c285, some c120, some c12, some c35, some c73, some c91, some c129, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p286 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked286 : lratChecker f286 p286 = .success := by decide +kernel
theorem unsat286 : Unsatisfiable (PosFin 31) f286 := by
  apply lratCheckerSound f286 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p286
  · intro a ha; simp [p286] at ha; subst a; trivial
  · exact checked286
theorem derived286 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c286 := by
  apply localUnsat_implies_entails f286 [c240, c282, c270, c115, c284, c285, c120, c12, c35, c73, c91, c129] c286 unsat286 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c284 := derived284 a h
  have h5 : Entails.eval a c285 := derived285 a h
  have h6 : Entails.eval a c120 := h 119 (by decide)
  have h7 : Entails.eval a c12 := h 11 (by decide)
  have h8 : Entails.eval a c35 := h 34 (by decide)
  have h9 : Entails.eval a c73 := h 72 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c287 : DefaultClause 31 := directClause [(⟨2, by decide⟩, false), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f287 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c282, some c286, some c112, some c8, some c91, some c195, some c18, some c161, some c198, some c188, some c54, some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p287 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked287 : lratChecker f287 p287 = .success := by decide +kernel
theorem unsat287 : Unsatisfiable (PosFin 31) f287 := by
  apply lratCheckerSound f287 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p287
  · intro a ha; simp [p287] at ha; subst a; trivial
  · exact checked287
theorem derived287 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c287 := by
  apply localUnsat_implies_entails f287 [c270, c282, c286, c112, c8, c91, c195, c18, c161, c198, c188, c54] c287 unsat287 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c286 := derived286 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  have h9 : Entails.eval a c198 := h 197 (by decide)
  have h10 : Entails.eval a c188 := h 187 (by decide)
  have h11 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c288 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f288 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c282, some c287, some c286, some c112, some c195, some c18, some c179, some c102, some c38, some c149, some c198, some c199, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p288 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked288 : lratChecker f288 p288 = .success := by decide +kernel
theorem unsat288 : Unsatisfiable (PosFin 31) f288 := by
  apply lratCheckerSound f288 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p288
  · intro a ha; simp [p288] at ha; subst a; trivial
  · exact checked288
theorem derived288 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c288 := by
  apply localUnsat_implies_entails f288 [c270, c282, c287, c286, c112, c195, c18, c179, c102, c38, c149, c198, c199] c288 unsat288 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c287 := derived287 a h
  have h3 : Entails.eval a c286 := derived286 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c195 := h 194 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c102 := h 101 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  have h10 : Entails.eval a c149 := h 148 (by decide)
  have h11 : Entails.eval a c198 := h 197 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c289 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f289 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c270, some c283, some c286, some c112, some c178, some c189, some c51, some c181, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p289 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked289 : lratChecker f289 p289 = .success := by decide +kernel
theorem unsat289 : Unsatisfiable (PosFin 31) f289 := by
  apply lratCheckerSound f289 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p289
  · intro a ha; simp [p289] at ha; subst a; trivial
  · exact checked289
theorem derived289 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c289 := by
  apply localUnsat_implies_entails f289 [c282, c270, c283, c286, c112, c178, c189, c51, c181] c289 unsat289 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c270 := derived270 a h
  have h2 : Entails.eval a c283 := derived283 a h
  have h3 : Entails.eval a c286 := derived286 a h
  have h4 : Entails.eval a c112 := h 111 (by decide)
  have h5 : Entails.eval a c178 := h 177 (by decide)
  have h6 : Entails.eval a c189 := h 188 (by decide)
  have h7 : Entails.eval a c51 := h 50 (by decide)
  have h8 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c290 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f290 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c283, some c266, some c282, some c289, some c118, some c195, some c288, some c179, some c133, some c38, some c202, some c169, some c168, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p290 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked290 : lratChecker f290 p290 = .success := by decide +kernel
theorem unsat290 : Unsatisfiable (PosFin 31) f290 := by
  apply lratCheckerSound f290 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p290
  · intro a ha; simp [p290] at ha; subst a; trivial
  · exact checked290
theorem derived290 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c290 := by
  apply localUnsat_implies_entails f290 [c240, c283, c266, c282, c289, c118, c195, c288, c179, c133, c38, c202, c169, c168] c290 unsat290 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c283 := derived283 a h
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c282 := derived282 a h
  have h4 : Entails.eval a c289 := derived289 a h
  have h5 : Entails.eval a c118 := h 117 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c288 := derived288 a h
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c133 := h 132 (by decide)
  have h10 : Entails.eval a c38 := h 37 (by decide)
  have h11 : Entails.eval a c202 := derived202 a h
  have h12 : Entails.eval a c169 := h 168 (by decide)
  have h13 : Entails.eval a c168 := h 167 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c291 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨27, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f291 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c283, some c282, some c286, some c112, some c163, some c290, some c195, some c18, some c110, some c70, some c179, some c53, some c197, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p291 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked291 : lratChecker f291 p291 = .success := by decide +kernel
theorem unsat291 : Unsatisfiable (PosFin 31) f291 := by
  apply lratCheckerSound f291 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p291
  · intro a ha; simp [p291] at ha; subst a; trivial
  · exact checked291
theorem derived291 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c291 := by
  apply localUnsat_implies_entails f291 [c283, c282, c286, c112, c163, c290, c195, c18, c110, c70, c179, c53, c197] c291 unsat291 (by rfl) a
  have h0 : Entails.eval a c283 := derived283 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c286 := derived286 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c163 := h 162 (by decide)
  have h5 : Entails.eval a c290 := derived290 a h
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c18 := h 17 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c70 := h 69 (by decide)
  have h10 : Entails.eval a c179 := h 178 (by decide)
  have h11 : Entails.eval a c53 := h 52 (by decide)
  have h12 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c292 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f292 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c282, some c283, some c266, some c290, some c286, some c112, some c35, some c178, some c189, some c162, some c109, some c125, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p292 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked292 : lratChecker f292 p292 = .success := by decide +kernel
theorem unsat292 : Unsatisfiable (PosFin 31) f292 := by
  apply lratCheckerSound f292 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p292
  · intro a ha; simp [p292] at ha; subst a; trivial
  · exact checked292
theorem derived292 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c292 := by
  apply localUnsat_implies_entails f292 [c270, c282, c283, c266, c290, c286, c112, c35, c178, c189, c162, c109, c125] c292 unsat292 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c283 := derived283 a h
  have h3 : Entails.eval a c266 := derived266 a h
  have h4 : Entails.eval a c290 := derived290 a h
  have h5 : Entails.eval a c286 := derived286 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c189 := h 188 (by decide)
  have h10 : Entails.eval a c162 := h 161 (by decide)
  have h11 : Entails.eval a c109 := h 108 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c293 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f293 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c240, some c292, some c118, some c291, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p293 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked293 : lratChecker f293 p293 = .success := by decide +kernel
theorem unsat293 : Unsatisfiable (PosFin 31) f293 := by
  apply lratCheckerSound f293 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p293
  · intro a ha; simp [p293] at ha; subst a; trivial
  · exact checked293
theorem derived293 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c293 := by
  apply localUnsat_implies_entails f293 [c282, c240, c292, c118, c291] c293 unsat293 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c292 := derived292 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c291 := derived291 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c294 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f294 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c283, some c270, some c293, some c290, some c286, some c112, some c178, some c189, some c171, some c65, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p294 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked294 : lratChecker f294 p294 = .success := by decide +kernel
theorem unsat294 : Unsatisfiable (PosFin 31) f294 := by
  apply lratCheckerSound f294 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p294
  · intro a ha; simp [p294] at ha; subst a; trivial
  · exact checked294
theorem derived294 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c294 := by
  apply localUnsat_implies_entails f294 [c282, c283, c270, c293, c290, c286, c112, c178, c189, c171, c65] c294 unsat294 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c283 := derived283 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c293 := derived293 a h
  have h4 : Entails.eval a c290 := derived290 a h
  have h5 : Entails.eval a c286 := derived286 a h
  have h6 : Entails.eval a c112 := h 111 (by decide)
  have h7 : Entails.eval a c178 := h 177 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c171 := h 170 (by decide)
  have h10 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c295 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f295 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c240, some c282, some c293, some c294, some c118, some c288, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p295 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked295 : lratChecker f295 p295 = .success := by decide +kernel
theorem unsat295 : Unsatisfiable (PosFin 31) f295 := by
  apply lratCheckerSound f295 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p295
  · intro a ha; simp [p295] at ha; subst a; trivial
  · exact checked295
theorem derived295 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c295 := by
  apply localUnsat_implies_entails f295 [c240, c282, c293, c294, c118, c288] c295 unsat295 (by rfl) a
  have h0 : Entails.eval a c240 := derived240 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c293 := derived293 a h
  have h3 : Entails.eval a c294 := derived294 a h
  have h4 : Entails.eval a c118 := h 117 (by decide)
  have h5 : Entails.eval a c288 := derived288 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c296 : DefaultClause 31 := directClause [(⟨20, by decide⟩, true), (⟨27, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f296 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c283, some c270, some c295, some c266, some c103, some c195, some c179, some c38, some c43, some c22, some c82, some c65, some c75, some c185, some c106, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p296 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked296 : lratChecker f296 p296 = .success := by decide +kernel
theorem unsat296 : Unsatisfiable (PosFin 31) f296 := by
  apply lratCheckerSound f296 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p296
  · intro a ha; simp [p296] at ha; subst a; trivial
  · exact checked296
theorem derived296 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c296 := by
  apply localUnsat_implies_entails f296 [c282, c283, c270, c295, c266, c103, c195, c179, c38, c43, c22, c82, c65, c75, c185, c106] c296 unsat296 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c283 := derived283 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c295 := derived295 a h
  have h4 : Entails.eval a c266 := derived266 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c195 := h 194 (by decide)
  have h7 : Entails.eval a c179 := h 178 (by decide)
  have h8 : Entails.eval a c38 := h 37 (by decide)
  have h9 : Entails.eval a c43 := h 42 (by decide)
  have h10 : Entails.eval a c22 := h 21 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c65 := h 64 (by decide)
  have h13 : Entails.eval a c75 := h 74 (by decide)
  have h14 : Entails.eval a c185 := h 184 (by decide)
  have h15 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c297 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f297 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c282, some c240, some c270, some c283, some c296, some c35, some c178, some c145, some c120, some c38, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p297 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked297 : lratChecker f297 p297 = .success := by decide +kernel
theorem unsat297 : Unsatisfiable (PosFin 31) f297 := by
  apply lratCheckerSound f297 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p297
  · intro a ha; simp [p297] at ha; subst a; trivial
  · exact checked297
theorem derived297 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c297 := by
  apply localUnsat_implies_entails f297 [c282, c240, c270, c283, c296, c35, c178, c145, c120, c38] c297 unsat297 (by rfl) a
  have h0 : Entails.eval a c282 := derived282 a h
  have h1 : Entails.eval a c240 := derived240 a h
  have h2 : Entails.eval a c270 := derived270 a h
  have h3 : Entails.eval a c283 := derived283 a h
  have h4 : Entails.eval a c296 := derived296 a h
  have h5 : Entails.eval a c35 := h 34 (by decide)
  have h6 : Entails.eval a c178 := h 177 (by decide)
  have h7 : Entails.eval a c145 := h 144 (by decide)
  have h8 : Entails.eval a c120 := h 119 (by decide)
  have h9 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c298 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f298 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c270, some c282, some c283, some c240, some c295, some c266, some c103, some c297, some c118, some c35, some c178, some c8, some c145, some c43, some c22, some c82, some c75, some c92, some c106, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p298 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked298 : lratChecker f298 p298 = .success := by decide +kernel
theorem unsat298 : Unsatisfiable (PosFin 31) f298 := by
  apply lratCheckerSound f298 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p298
  · intro a ha; simp [p298] at ha; subst a; trivial
  · exact checked298
theorem derived298 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c298 := by
  apply localUnsat_implies_entails f298 [c270, c282, c283, c240, c295, c266, c103, c297, c118, c35, c178, c8, c145, c43, c22, c82, c75, c92, c106] c298 unsat298 (by rfl) a
  have h0 : Entails.eval a c270 := derived270 a h
  have h1 : Entails.eval a c282 := derived282 a h
  have h2 : Entails.eval a c283 := derived283 a h
  have h3 : Entails.eval a c240 := derived240 a h
  have h4 : Entails.eval a c295 := derived295 a h
  have h5 : Entails.eval a c266 := derived266 a h
  have h6 : Entails.eval a c103 := h 102 (by decide)
  have h7 : Entails.eval a c297 := derived297 a h
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c178 := h 177 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c145 := h 144 (by decide)
  have h13 : Entails.eval a c43 := h 42 (by decide)
  have h14 : Entails.eval a c22 := h 21 (by decide)
  have h15 : Entails.eval a c82 := h 81 (by decide)
  have h16 : Entails.eval a c75 := h 74 (by decide)
  have h17 : Entails.eval a c92 := h 91 (by decide)
  have h18 : Entails.eval a c106 := h 105 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c299 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f299 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c298, some c283, some c295, some c95, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p299 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked299 : lratChecker f299 p299 = .success := by decide +kernel
theorem unsat299 : Unsatisfiable (PosFin 31) f299 := by
  apply lratCheckerSound f299 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p299
  · intro a ha; simp [p299] at ha; subst a; trivial
  · exact checked299
theorem derived299 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c299 := by
  apply localUnsat_implies_entails f299 [c298, c283, c295, c95] c299 unsat299 (by rfl) a
  have h0 : Entails.eval a c298 := derived298 a h
  have h1 : Entails.eval a c283 := derived283 a h
  have h2 : Entails.eval a c295 := derived295 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
#print axioms derived299

end CochromaticTwenty.Certificates.Z12Direct_5_4_4
