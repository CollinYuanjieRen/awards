import MerLeanExperiment.Certificates.Z12Direct_5_3_0.Inputs

/-! Generated from the actual pinned z12direct_5_3_0-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_3_0
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c198 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f198 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c16, some c32, some c85, some c51, some c134, some c142, some c46, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p198 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked198 : lratChecker f198 p198 = .success := by decide +kernel
theorem unsat198 : Unsatisfiable (PosFin 31) f198 := by
  apply lratCheckerSound f198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p198
  · intro a ha; simp [p198] at ha; subst a; trivial
  · exact checked198
theorem derived198 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c198 := by
  apply localUnsat_implies_entails f198 [c71, c16, c32, c85, c51, c134, c142, c46] c198 unsat198 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  have h4 : Entails.eval a c51 := h 50 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c142 := h 141 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c199 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f199 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c71, some c16, some c198, some c95, some c5, some c46, some c51, some c66, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p199 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked199 : lratChecker f199 p199 = .success := by decide +kernel
theorem unsat199 : Unsatisfiable (PosFin 31) f199 := by
  apply lratCheckerSound f199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p199
  · intro a ha; simp [p199] at ha; subst a; trivial
  · exact checked199
theorem derived199 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c199 := by
  apply localUnsat_implies_entails f199 [c71, c16, c198, c95, c5, c46, c51, c66] c199 unsat199 (by rfl) a
  have h0 : Entails.eval a c71 := h 70 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c198 := derived198 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c46 := h 45 (by decide)
  have h6 : Entails.eval a c51 := h 50 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c200 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c199, some c71, some c16, some c94, some c5, some c51, some c25, some c135, some c26, some c118, some c168, some c125, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked200 : lratChecker f200 p200 = .success := by decide +kernel
theorem unsat200 : Unsatisfiable (PosFin 31) f200 := by
  apply lratCheckerSound f200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p200
  · intro a ha; simp [p200] at ha; subst a; trivial
  · exact checked200
theorem derived200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c200 := by
  apply localUnsat_implies_entails f200 [c199, c71, c16, c94, c5, c51, c25, c135, c26, c118, c168, c125] c200 unsat200 (by rfl) a
  have h0 : Entails.eval a c199 := derived199 a h
  have h1 : Entails.eval a c71 := h 70 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c51 := h 50 (by decide)
  have h6 : Entails.eval a c25 := h 24 (by decide)
  have h7 : Entails.eval a c135 := h 134 (by decide)
  have h8 : Entails.eval a c26 := h 25 (by decide)
  have h9 : Entails.eval a c118 := h 117 (by decide)
  have h10 : Entails.eval a c168 := h 167 (by decide)
  have h11 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c201 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨23, by decide⟩, false), (⟨30, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c199, some c200, some c32, some c41, some c68, some c58, some c73, some c82, some c2, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked201 : lratChecker f201 p201 = .success := by decide +kernel
theorem unsat201 : Unsatisfiable (PosFin 31) f201 := by
  apply lratCheckerSound f201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p201
  · intro a ha; simp [p201] at ha; subst a; trivial
  · exact checked201
theorem derived201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c201 := by
  apply localUnsat_implies_entails f201 [c199, c200, c32, c41, c68, c58, c73, c82, c2] c201 unsat201 (by rfl) a
  have h0 : Entails.eval a c199 := derived199 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c32 := h 31 (by decide)
  have h3 : Entails.eval a c41 := h 40 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  have h7 : Entails.eval a c82 := h 81 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c202 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c5, some c61, some c16, some c127, some c122, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked202 : lratChecker f202 p202 = .success := by decide +kernel
theorem unsat202 : Unsatisfiable (PosFin 31) f202 := by
  apply lratCheckerSound f202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p202
  · intro a ha; simp [p202] at ha; subst a; trivial
  · exact checked202
theorem derived202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c202 := by
  apply localUnsat_implies_entails f202 [c33, c5, c61, c16, c127, c122] c202 unsat202 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c127 := h 126 (by decide)
  have h5 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c203 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c201, some c33, some c26, some c50, some c122, some c78, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked203 : lratChecker f203 p203 = .success := by decide +kernel
theorem unsat203 : Unsatisfiable (PosFin 31) f203 := by
  apply lratCheckerSound f203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p203
  · intro a ha; simp [p203] at ha; subst a; trivial
  · exact checked203
theorem derived203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c203 := by
  apply localUnsat_implies_entails f203 [c201, c33, c26, c50, c122, c78] c203 unsat203 (by rfl) a
  have h0 : Entails.eval a c201 := derived201 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c122 := h 121 (by decide)
  have h5 : Entails.eval a c78 := h 77 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c204 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c201, some c33, some c203, some c5, some c202, some c75, some c16, some c104, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked204 : lratChecker f204 p204 = .success := by decide +kernel
theorem unsat204 : Unsatisfiable (PosFin 31) f204 := by
  apply lratCheckerSound f204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p204
  · intro a ha; simp [p204] at ha; subst a; trivial
  · exact checked204
theorem derived204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c204 := by
  apply localUnsat_implies_entails f204 [c201, c33, c203, c5, c202, c75, c16, c104] c204 unsat204 (by rfl) a
  have h0 : Entails.eval a c201 := derived201 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c203 := derived203 a h
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c202 := derived202 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c104 := h 103 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c205 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨24, by decide⟩, true), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c44, some c15, some c16, some c42, some c68, some c12, some c83, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked205 : lratChecker f205 p205 = .success := by decide +kernel
theorem unsat205 : Unsatisfiable (PosFin 31) f205 := by
  apply lratCheckerSound f205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p205
  · intro a ha; simp [p205] at ha; subst a; trivial
  · exact checked205
theorem derived205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c205 := by
  apply localUnsat_implies_entails f205 [c5, c44, c15, c16, c42, c68, c12, c83] c205 unsat205 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c44 := h 43 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c42 := h 41 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c12 := h 11 (by decide)
  have h7 : Entails.eval a c83 := h 82 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c206 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c204, some c25, some c26, some c149, some c128, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked206 : lratChecker f206 p206 = .success := by decide +kernel
theorem unsat206 : Unsatisfiable (PosFin 31) f206 := by
  apply lratCheckerSound f206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p206
  · intro a ha; simp [p206] at ha; subst a; trivial
  · exact checked206
theorem derived206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c206 := by
  apply localUnsat_implies_entails f206 [c204, c25, c26, c149, c128] c206 unsat206 (by rfl) a
  have h0 : Entails.eval a c204 := derived204 a h
  have h1 : Entails.eval a c25 := h 24 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c149 := h 148 (by decide)
  have h4 : Entails.eval a c128 := h 127 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c207 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c204, some c32, some c33, some c102, some c76, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked207 : lratChecker f207 p207 = .success := by decide +kernel
theorem unsat207 : Unsatisfiable (PosFin 31) f207 := by
  apply lratCheckerSound f207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p207
  · intro a ha; simp [p207] at ha; subst a; trivial
  · exact checked207
theorem derived207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c207 := by
  apply localUnsat_implies_entails f207 [c204, c32, c33, c102, c76] c207 unsat207 (by rfl) a
  have h0 : Entails.eval a c204 := derived204 a h
  have h1 : Entails.eval a c32 := h 31 (by decide)
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c102 := h 101 (by decide)
  have h4 : Entails.eval a c76 := h 75 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c208 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨11, by decide⟩, true), (⟨30, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c205, some c5, some c202, some c16, some c71, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked208 : lratChecker f208 p208 = .success := by decide +kernel
theorem unsat208 : Unsatisfiable (PosFin 31) f208 := by
  apply lratCheckerSound f208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p208
  · intro a ha; simp [p208] at ha; subst a; trivial
  · exact checked208
theorem derived208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c208 := by
  apply localUnsat_implies_entails f208 [c205, c5, c202, c16, c71] c208 unsat208 (by rfl) a
  have h0 : Entails.eval a c205 := derived205 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c202 := derived202 a h
  have h3 : Entails.eval a c16 := h 15 (by decide)
  have h4 : Entails.eval a c71 := h 70 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c209 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c206, some c207, some c208, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked209 : lratChecker f209 p209 = .success := by decide +kernel
theorem unsat209 : Unsatisfiable (PosFin 31) f209 := by
  apply lratCheckerSound f209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p209
  · intro a ha; simp [p209] at ha; subst a; trivial
  · exact checked209
theorem derived209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c209 := by
  apply localUnsat_implies_entails f209 [c206, c207, c208] c209 unsat209 (by rfl) a
  have h0 : Entails.eval a c206 := derived206 a h
  have h1 : Entails.eval a c207 := derived207 a h
  have h2 : Entails.eval a c208 := derived208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c210 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c43, some c5, some c16, some c209, some c96, some c97, some c6, some c36, some c24, some c53, some c136, some c117, some c174, some c123, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked210 : lratChecker f210 p210 = .success := by decide +kernel
theorem unsat210 : Unsatisfiable (PosFin 31) f210 := by
  apply lratCheckerSound f210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p210
  · intro a ha; simp [p210] at ha; subst a; trivial
  · exact checked210
theorem derived210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c210 := by
  apply localUnsat_implies_entails f210 [c43, c5, c16, c209, c96, c97, c6, c36, c24, c53, c136, c117, c174, c123] c210 unsat210 (by rfl) a
  have h0 : Entails.eval a c43 := h 42 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c209 := derived209 a h
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c36 := h 35 (by decide)
  have h8 : Entails.eval a c24 := h 23 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c136 := h 135 (by decide)
  have h11 : Entails.eval a c117 := h 116 (by decide)
  have h12 : Entails.eval a c174 := h 173 (by decide)
  have h13 : Entails.eval a c123 := h 122 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c211 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c16, some c209, some c43, some c210, some c75, some c61, some c67, some c53, some c55, some c80, some c143, some c144, some c171, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked211 : lratChecker f211 p211 = .success := by decide +kernel
theorem unsat211 : Unsatisfiable (PosFin 31) f211 := by
  apply lratCheckerSound f211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p211
  · intro a ha; simp [p211] at ha; subst a; trivial
  · exact checked211
theorem derived211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c211 := by
  apply localUnsat_implies_entails f211 [c5, c16, c209, c43, c210, c75, c61, c67, c53, c55, c80, c143, c144, c171] c211 unsat211 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c209 := derived209 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c210 := derived210 a h
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c53 := h 52 (by decide)
  have h9 : Entails.eval a c55 := h 54 (by decide)
  have h10 : Entails.eval a c80 := h 79 (by decide)
  have h11 : Entails.eval a c143 := h 142 (by decide)
  have h12 : Entails.eval a c144 := h 143 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c212 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c5, some c16, some c211, some c150, some c104, some c127, some c75, some c6, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked212 : lratChecker f212 p212 = .success := by decide +kernel
theorem unsat212 : Unsatisfiable (PosFin 31) f212 := by
  apply lratCheckerSound f212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p212
  · intro a ha; simp [p212] at ha; subst a; trivial
  · exact checked212
theorem derived212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c212 := by
  apply localUnsat_implies_entails f212 [c5, c16, c211, c150, c104, c127, c75, c6] c212 unsat212 (by rfl) a
  have h0 : Entails.eval a c5 := h 4 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c211 := derived211 a h
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c104 := h 103 (by decide)
  have h5 : Entails.eval a c127 := h 126 (by decide)
  have h6 : Entails.eval a c75 := h 74 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c213 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨24, by decide⟩, true), (⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c26, some c16, some c128, some c151, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked213 : lratChecker f213 p213 = .success := by decide +kernel
theorem unsat213 : Unsatisfiable (PosFin 31) f213 := by
  apply lratCheckerSound f213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p213
  · intro a ha; simp [p213] at ha; subst a; trivial
  · exact checked213
theorem derived213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c213 := by
  apply localUnsat_implies_entails f213 [c26, c16, c128, c151] c213 unsat213 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c16 := h 15 (by decide)
  have h2 : Entails.eval a c128 := h 127 (by decide)
  have h3 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c214 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c212, some c209, some c213, some c69, some c95, some c162, some c93, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked214 : lratChecker f214 p214 = .success := by decide +kernel
theorem unsat214 : Unsatisfiable (PosFin 31) f214 := by
  apply lratCheckerSound f214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p214
  · intro a ha; simp [p214] at ha; subst a; trivial
  · exact checked214
theorem derived214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c214 := by
  apply localUnsat_implies_entails f214 [c212, c209, c213, c69, c95, c162, c93] c214 unsat214 (by rfl) a
  have h0 : Entails.eval a c212 := derived212 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c213 := derived213 a h
  have h3 : Entails.eval a c69 := h 68 (by decide)
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c215 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨22, by decide⟩, false), (⟨21, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c143, some c144, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked215 : lratChecker f215 p215 = .success := by decide +kernel
theorem unsat215 : Unsatisfiable (PosFin 31) f215 := by
  apply lratCheckerSound f215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p215
  · intro a ha; simp [p215] at ha; subst a; trivial
  · exact checked215
theorem derived215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c215 := by
  apply localUnsat_implies_entails f215 [c143, c144] c215 unsat215 (by rfl) a
  have h0 : Entails.eval a c143 := h 142 (by decide)
  have h1 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c216 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c212, some c26, some c209, some c69, some c94, some c36, some c215, some c135, some c84, some c14, some c46, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked216 : lratChecker f216 p216 = .success := by decide +kernel
theorem unsat216 : Unsatisfiable (PosFin 31) f216 := by
  apply lratCheckerSound f216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p216
  · intro a ha; simp [p216] at ha; subst a; trivial
  · exact checked216
theorem derived216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c216 := by
  apply localUnsat_implies_entails f216 [c214, c212, c26, c209, c69, c94, c36, c215, c135, c84, c14, c46] c216 unsat216 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c212 := derived212 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c209 := derived209 a h
  have h4 : Entails.eval a c69 := h 68 (by decide)
  have h5 : Entails.eval a c94 := h 93 (by decide)
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c215 := derived215 a h
  have h8 : Entails.eval a c135 := h 134 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c14 := h 13 (by decide)
  have h11 : Entails.eval a c46 := h 45 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c217 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c212, some c26, some c214, some c216, some c16, some c128, some c6, some c63, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked217 : lratChecker f217 p217 = .success := by decide +kernel
theorem unsat217 : Unsatisfiable (PosFin 31) f217 := by
  apply lratCheckerSound f217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p217
  · intro a ha; simp [p217] at ha; subst a; trivial
  · exact checked217
theorem derived217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c217 := by
  apply localUnsat_implies_entails f217 [c212, c26, c214, c216, c16, c128, c6, c63] c217 unsat217 (by rfl) a
  have h0 : Entails.eval a c212 := derived212 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c214 := derived214 a h
  have h3 : Entails.eval a c216 := derived216 a h
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c128 := h 127 (by decide)
  have h6 : Entails.eval a c6 := h 5 (by decide)
  have h7 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c218 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c217, some c33, some c26, some c6, some c16, some c131, some c64, some c149, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked218 : lratChecker f218 p218 = .success := by decide +kernel
theorem unsat218 : Unsatisfiable (PosFin 31) f218 := by
  apply lratCheckerSound f218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p218
  · intro a ha; simp [p218] at ha; subst a; trivial
  · exact checked218
theorem derived218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c218 := by
  apply localUnsat_implies_entails f218 [c217, c33, c26, c6, c16, c131, c64, c149] c218 unsat218 (by rfl) a
  have h0 : Entails.eval a c217 := derived217 a h
  have h1 : Entails.eval a c33 := h 32 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c16 := h 15 (by decide)
  have h5 : Entails.eval a c131 := h 130 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c219 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨5, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c218, some c217, some c33, some c209, some c130, some c85, some c79, some c129, some c67, some c134, some c102, some c77, some c46, some c176, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked219 : lratChecker f219 p219 = .success := by decide +kernel
theorem unsat219 : Unsatisfiable (PosFin 31) f219 := by
  apply lratCheckerSound f219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p219
  · intro a ha; simp [p219] at ha; subst a; trivial
  · exact checked219
theorem derived219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c219 := by
  apply localUnsat_implies_entails f219 [c218, c217, c33, c209, c130, c85, c79, c129, c67, c134, c102, c77, c46, c176] c219 unsat219 (by rfl) a
  have h0 : Entails.eval a c218 := derived218 a h
  have h1 : Entails.eval a c217 := derived217 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c209 := derived209 a h
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c79 := h 78 (by decide)
  have h7 : Entails.eval a c129 := h 128 (by decide)
  have h8 : Entails.eval a c67 := h 66 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c102 := h 101 (by decide)
  have h11 : Entails.eval a c77 := h 76 (by decide)
  have h12 : Entails.eval a c46 := h 45 (by decide)
  have h13 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c220 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c218, some c217, some c33, some c209, some c119, some c219, some c87, some c6, some c82, some c134, some c133, some c8, some c132, some c184, some c187, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked220 : lratChecker f220 p220 = .success := by decide +kernel
theorem unsat220 : Unsatisfiable (PosFin 31) f220 := by
  apply lratCheckerSound f220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p220
  · intro a ha; simp [p220] at ha; subst a; trivial
  · exact checked220
theorem derived220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c220 := by
  apply localUnsat_implies_entails f220 [c218, c217, c33, c209, c119, c219, c87, c6, c82, c134, c133, c8, c132, c184, c187] c220 unsat220 (by rfl) a
  have h0 : Entails.eval a c218 := derived218 a h
  have h1 : Entails.eval a c217 := derived217 a h
  have h2 : Entails.eval a c33 := h 32 (by decide)
  have h3 : Entails.eval a c209 := derived209 a h
  have h4 : Entails.eval a c119 := h 118 (by decide)
  have h5 : Entails.eval a c219 := derived219 a h
  have h6 : Entails.eval a c87 := h 86 (by decide)
  have h7 : Entails.eval a c6 := h 5 (by decide)
  have h8 : Entails.eval a c82 := h 81 (by decide)
  have h9 : Entails.eval a c134 := h 133 (by decide)
  have h10 : Entails.eval a c133 := h 132 (by decide)
  have h11 : Entails.eval a c8 := h 7 (by decide)
  have h12 : Entails.eval a c132 := h 131 (by decide)
  have h13 : Entails.eval a c184 := h 183 (by decide)
  have h14 : Entails.eval a c187 := h 186 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c221 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c33, some c220, some c16, some c76, some c6, some c54, some c105, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked221 : lratChecker f221 p221 = .success := by decide +kernel
theorem unsat221 : Unsatisfiable (PosFin 31) f221 := by
  apply lratCheckerSound f221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p221
  · intro a ha; simp [p221] at ha; subst a; trivial
  · exact checked221
theorem derived221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c221 := by
  apply localUnsat_implies_entails f221 [c33, c220, c16, c76, c6, c54, c105] c221 unsat221 (by rfl) a
  have h0 : Entails.eval a c33 := h 32 (by decide)
  have h1 : Entails.eval a c220 := derived220 a h
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c76 := h 75 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c105 := h 104 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c222 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c217, some c221, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked222 : lratChecker f222 p222 = .success := by decide +kernel
theorem unsat222 : Unsatisfiable (PosFin 31) f222 := by
  apply lratCheckerSound f222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p222
  · intro a ha; simp [p222] at ha; subst a; trivial
  · exact checked222
theorem derived222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c222 := by
  apply localUnsat_implies_entails f222 [c217, c221] c222 unsat222 (by rfl) a
  have h0 : Entails.eval a c217 := derived217 a h
  have h1 : Entails.eval a c221 := derived221 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c223 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c194, some c114, some c86, some c136, some c6, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked223 : lratChecker f223 p223 = .success := by decide +kernel
theorem unsat223 : Unsatisfiable (PosFin 31) f223 := by
  apply lratCheckerSound f223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p223
  · intro a ha; simp [p223] at ha; subst a; trivial
  · exact checked223
theorem derived223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c223 := by
  apply localUnsat_implies_entails f223 [c222, c194, c114, c86, c136, c6] c223 unsat223 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c86 := h 85 (by decide)
  have h4 : Entails.eval a c136 := h 135 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c224 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨6, by decide⟩, false), (⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c112, some c64, some c58, some c138, some c161, some c166, some c88, some c115, some c36, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked224 : lratChecker f224 p224 = .success := by decide +kernel
theorem unsat224 : Unsatisfiable (PosFin 31) f224 := by
  apply lratCheckerSound f224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p224
  · intro a ha; simp [p224] at ha; subst a; trivial
  · exact checked224
theorem derived224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c224 := by
  apply localUnsat_implies_entails f224 [c112, c64, c58, c138, c161, c166, c88, c115, c36] c224 unsat224 (by rfl) a
  have h0 : Entails.eval a c112 := h 111 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  have h2 : Entails.eval a c58 := h 57 (by decide)
  have h3 : Entails.eval a c138 := h 137 (by decide)
  have h4 : Entails.eval a c161 := h 160 (by decide)
  have h5 : Entails.eval a c166 := h 165 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c115 := h 114 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c225 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c194, some c223, some c112, some c224, some c136, some c62, some c7, some c130, some c131, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked225 : lratChecker f225 p225 = .success := by decide +kernel
theorem unsat225 : Unsatisfiable (PosFin 31) f225 := by
  apply lratCheckerSound f225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p225
  · intro a ha; simp [p225] at ha; subst a; trivial
  · exact checked225
theorem derived225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c225 := by
  apply localUnsat_implies_entails f225 [c222, c194, c223, c112, c224, c136, c62, c7, c130, c131] c225 unsat225 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c223 := derived223 a h
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c224 := derived224 a h
  have h5 : Entails.eval a c136 := h 135 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c226 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c225, some c222, some c194, some c112, some c79, some c84, some c134, some c46, some c51, some c64, some c142, some c58, some c141, some c153, some c19, some c108, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked226 : lratChecker f226 p226 = .success := by decide +kernel
theorem unsat226 : Unsatisfiable (PosFin 31) f226 := by
  apply lratCheckerSound f226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p226
  · intro a ha; simp [p226] at ha; subst a; trivial
  · exact checked226
theorem derived226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c226 := by
  apply localUnsat_implies_entails f226 [c225, c222, c194, c112, c79, c84, c134, c46, c51, c64, c142, c58, c141, c153, c19, c108] c226 unsat226 (by rfl) a
  have h0 : Entails.eval a c225 := derived225 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c112 := h 111 (by decide)
  have h4 : Entails.eval a c79 := h 78 (by decide)
  have h5 : Entails.eval a c84 := h 83 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  have h7 : Entails.eval a c46 := h 45 (by decide)
  have h8 : Entails.eval a c51 := h 50 (by decide)
  have h9 : Entails.eval a c64 := h 63 (by decide)
  have h10 : Entails.eval a c142 := h 141 (by decide)
  have h11 : Entails.eval a c58 := h 57 (by decide)
  have h12 : Entails.eval a c141 := h 140 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  have h15 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c227 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c226, some c225, some c222, some c121, some c6, some c72, some c84, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked227 : lratChecker f227 p227 = .success := by decide +kernel
theorem unsat227 : Unsatisfiable (PosFin 31) f227 := by
  apply lratCheckerSound f227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p227
  · intro a ha; simp [p227] at ha; subst a; trivial
  · exact checked227
theorem derived227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c227 := by
  apply localUnsat_implies_entails f227 [c226, c225, c222, c121, c6, c72, c84] c227 unsat227 (by rfl) a
  have h0 : Entails.eval a c226 := derived226 a h
  have h1 : Entails.eval a c225 := derived225 a h
  have h2 : Entails.eval a c222 := derived222 a h
  have h3 : Entails.eval a c121 := h 120 (by decide)
  have h4 : Entails.eval a c6 := h 5 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c84 := h 83 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c228 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f228 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c194, some c227, some c62, some c225, some c134, some c226, some c114, some c110, some c30, some c74, some c72, some c162, some c150, some c178, some c195, some c28, some c182, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p228 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked228 : lratChecker f228 p228 = .success := by decide +kernel
theorem unsat228 : Unsatisfiable (PosFin 31) f228 := by
  apply lratCheckerSound f228 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p228
  · intro a ha; simp [p228] at ha; subst a; trivial
  · exact checked228
theorem derived228 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c228 := by
  apply localUnsat_implies_entails f228 [c222, c194, c227, c62, c225, c134, c226, c114, c110, c30, c74, c72, c162, c150, c178, c195, c28, c182] c228 unsat228 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c227 := derived227 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c225 := derived225 a h
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c226 := derived226 a h
  have h7 : Entails.eval a c114 := h 113 (by decide)
  have h8 : Entails.eval a c110 := h 109 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c74 := h 73 (by decide)
  have h11 : Entails.eval a c72 := h 71 (by decide)
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c178 := h 177 (by decide)
  have h15 : Entails.eval a c195 := h 194 (by decide)
  have h16 : Entails.eval a c28 := h 27 (by decide)
  have h17 : Entails.eval a c182 := h 181 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c229 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f229 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c225, some c226, some c227, some c134, some c228, some c70, some c119, some c124, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p229 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked229 : lratChecker f229 p229 = .success := by decide +kernel
theorem unsat229 : Unsatisfiable (PosFin 31) f229 := by
  apply lratCheckerSound f229 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p229
  · intro a ha; simp [p229] at ha; subst a; trivial
  · exact checked229
theorem derived229 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c229 := by
  apply localUnsat_implies_entails f229 [c222, c225, c226, c227, c134, c228, c70, c119, c124] c229 unsat229 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c225 := derived225 a h
  have h2 : Entails.eval a c226 := derived226 a h
  have h3 : Entails.eval a c227 := derived227 a h
  have h4 : Entails.eval a c134 := h 133 (by decide)
  have h5 : Entails.eval a c228 := derived228 a h
  have h6 : Entails.eval a c70 := h 69 (by decide)
  have h7 : Entails.eval a c119 := h 118 (by decide)
  have h8 : Entails.eval a c124 := h 123 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c230 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f230 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c132, some c123, some c116, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p230 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked230 : lratChecker f230 p230 = .success := by decide +kernel
theorem unsat230 : Unsatisfiable (PosFin 31) f230 := by
  apply lratCheckerSound f230 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p230
  · intro a ha; simp [p230] at ha; subst a; trivial
  · exact checked230
theorem derived230 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c230 := by
  apply localUnsat_implies_entails f230 [c132, c123, c116] c230 unsat230 (by rfl) a
  have h0 : Entails.eval a c132 := h 131 (by decide)
  have h1 : Entails.eval a c123 := h 122 (by decide)
  have h2 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c231 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f231 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c104, some c53, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p231 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked231 : lratChecker f231 p231 = .success := by decide +kernel
theorem unsat231 : Unsatisfiable (PosFin 31) f231 := by
  apply lratCheckerSound f231 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p231
  · intro a ha; simp [p231] at ha; subst a; trivial
  · exact checked231
theorem derived231 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c231 := by
  apply localUnsat_implies_entails f231 [c104, c53] c231 unsat231 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c232 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f232 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c231, some c222, some c132, some c230, some c70, some c35, some c98, some c1, some c47, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p232 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked232 : lratChecker f232 p232 = .success := by decide +kernel
theorem unsat232 : Unsatisfiable (PosFin 31) f232 := by
  apply lratCheckerSound f232 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p232
  · intro a ha; simp [p232] at ha; subst a; trivial
  · exact checked232
theorem derived232 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c232 := by
  apply localUnsat_implies_entails f232 [c229, c231, c222, c132, c230, c70, c35, c98, c1, c47] c232 unsat232 (by rfl) a
  have h0 : Entails.eval a c229 := derived229 a h
  have h1 : Entails.eval a c231 := derived231 a h
  have h2 : Entails.eval a c222 := derived222 a h
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c230 := derived230 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c35 := h 34 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c47 := h 46 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c233 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false), (⟨3, by decide⟩, true), (⟨15, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f233 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c145, some c56, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p233 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked233 : lratChecker f233 p233 = .success := by decide +kernel
theorem unsat233 : Unsatisfiable (PosFin 31) f233 := by
  apply lratCheckerSound f233 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p233
  · intro a ha; simp [p233] at ha; subst a; trivial
  · exact checked233
theorem derived233 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c233 := by
  apply localUnsat_implies_entails f233 [c145, c56] c233 unsat233 (by rfl) a
  have h0 : Entails.eval a c145 := h 144 (by decide)
  have h1 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c234 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f234 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c222, some c194, some c231, some c232, some c134, some c136, some c159, some c233, some c18, some c103, some c52, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p234 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked234 : lratChecker f234 p234 = .success := by decide +kernel
theorem unsat234 : Unsatisfiable (PosFin 31) f234 := by
  apply lratCheckerSound f234 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p234
  · intro a ha; simp [p234] at ha; subst a; trivial
  · exact checked234
theorem derived234 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c234 := by
  apply localUnsat_implies_entails f234 [c229, c222, c194, c231, c232, c134, c136, c159, c233, c18, c103, c52] c234 unsat234 (by rfl) a
  have h0 : Entails.eval a c229 := derived229 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c231 := derived231 a h
  have h4 : Entails.eval a c232 := derived232 a h
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  have h7 : Entails.eval a c159 := h 158 (by decide)
  have h8 : Entails.eval a c233 := derived233 a h
  have h9 : Entails.eval a c18 := h 17 (by decide)
  have h10 : Entails.eval a c103 := h 102 (by decide)
  have h11 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c235 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f235 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c222, some c194, some c234, some c121, some c6, some c144, some c38, some c69, some c31, some c170, some c86, some c104, some c159, some c43, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p235 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked235 : lratChecker f235 p235 = .success := by decide +kernel
theorem unsat235 : Unsatisfiable (PosFin 31) f235 := by
  apply lratCheckerSound f235 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p235
  · intro a ha; simp [p235] at ha; subst a; trivial
  · exact checked235
theorem derived235 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c235 := by
  apply localUnsat_implies_entails f235 [c229, c222, c194, c234, c121, c6, c144, c38, c69, c31, c170, c86, c104, c159, c43] c235 unsat235 (by rfl) a
  have h0 : Entails.eval a c229 := derived229 a h
  have h1 : Entails.eval a c222 := derived222 a h
  have h2 : Entails.eval a c194 := h 193 (by decide)
  have h3 : Entails.eval a c234 := derived234 a h
  have h4 : Entails.eval a c121 := h 120 (by decide)
  have h5 : Entails.eval a c6 := h 5 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c69 := h 68 (by decide)
  have h9 : Entails.eval a c31 := h 30 (by decide)
  have h10 : Entails.eval a c170 := h 169 (by decide)
  have h11 : Entails.eval a c86 := h 85 (by decide)
  have h12 : Entails.eval a c104 := h 103 (by decide)
  have h13 : Entails.eval a c159 := h 158 (by decide)
  have h14 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c236 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f236 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c235, some c229, some c78, some c77, some c130, some c18, some c129, some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p236 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked236 : lratChecker f236 p236 = .success := by decide +kernel
theorem unsat236 : Unsatisfiable (PosFin 31) f236 := by
  apply lratCheckerSound f236 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p236
  · intro a ha; simp [p236] at ha; subst a; trivial
  · exact checked236
theorem derived236 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c236 := by
  apply localUnsat_implies_entails f236 [c235, c229, c78, c77, c130, c18, c129] c236 unsat236 (by rfl) a
  have h0 : Entails.eval a c235 := derived235 a h
  have h1 : Entails.eval a c229 := derived229 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c77 := h 76 (by decide)
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c18 := h 17 (by decide)
  have h6 : Entails.eval a c129 := h 128 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c237 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f237 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c229, some c235, some c78, some c222, some c194, some c236, some c50, some c131, some c77, some c20, some c46, some c49, some c19, some c186, some c147, some c155, some c183, some c181, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p237 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked237 : lratChecker f237 p237 = .success := by decide +kernel
theorem unsat237 : Unsatisfiable (PosFin 31) f237 := by
  apply lratCheckerSound f237 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p237
  · intro a ha; simp [p237] at ha; subst a; trivial
  · exact checked237
theorem derived237 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c237 := by
  apply localUnsat_implies_entails f237 [c229, c235, c78, c222, c194, c236, c50, c131, c77, c20, c46, c49, c19, c186, c147, c155, c183, c181] c237 unsat237 (by rfl) a
  have h0 : Entails.eval a c229 := derived229 a h
  have h1 : Entails.eval a c235 := derived235 a h
  have h2 : Entails.eval a c78 := h 77 (by decide)
  have h3 : Entails.eval a c222 := derived222 a h
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c236 := derived236 a h
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c77 := h 76 (by decide)
  have h9 : Entails.eval a c20 := h 19 (by decide)
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c49 := h 48 (by decide)
  have h12 : Entails.eval a c19 := h 18 (by decide)
  have h13 : Entails.eval a c186 := h 185 (by decide)
  have h14 : Entails.eval a c147 := h 146 (by decide)
  have h15 : Entails.eval a c155 := h 154 (by decide)
  have h16 : Entails.eval a c183 := h 182 (by decide)
  have h17 : Entails.eval a c181 := h 180 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c238 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f238 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c194, some c229, some c235, some c78, some c236, some c157, some c237, some c65, some c146, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p238 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked238 : lratChecker f238 p238 = .success := by decide +kernel
theorem unsat238 : Unsatisfiable (PosFin 31) f238 := by
  apply lratCheckerSound f238 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p238
  · intro a ha; simp [p238] at ha; subst a; trivial
  · exact checked238
theorem derived238 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c238 := by
  apply localUnsat_implies_entails f238 [c222, c194, c229, c235, c78, c236, c157, c237, c65, c146] c238 unsat238 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c194 := h 193 (by decide)
  have h2 : Entails.eval a c229 := derived229 a h
  have h3 : Entails.eval a c235 := derived235 a h
  have h4 : Entails.eval a c78 := h 77 (by decide)
  have h5 : Entails.eval a c236 := derived236 a h
  have h6 : Entails.eval a c157 := h 156 (by decide)
  have h7 : Entails.eval a c237 := derived237 a h
  have h8 : Entails.eval a c65 := h 64 (by decide)
  have h9 : Entails.eval a c146 := h 145 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c239 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f239 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c188, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p239 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked239 : lratChecker f239 p239 = .success := by decide +kernel
theorem unsat239 : Unsatisfiable (PosFin 31) f239 := by
  apply lratCheckerSound f239 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p239
  · intro a ha; simp [p239] at ha; subst a; trivial
  · exact checked239
theorem derived239 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c239 := by
  apply localUnsat_implies_entails f239 [c238, c188] c239 unsat239 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c240 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f240 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c23, some c53, some c65, some c194, some c146, some c135, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p240 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked240 : lratChecker f240 p240 = .success := by decide +kernel
theorem unsat240 : Unsatisfiable (PosFin 31) f240 := by
  apply lratCheckerSound f240 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p240
  · intro a ha; simp [p240] at ha; subst a; trivial
  · exact checked240
theorem derived240 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c240 := by
  apply localUnsat_implies_entails f240 [c239, c23, c53, c65, c194, c146, c135] c240 unsat240 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c53 := h 52 (by decide)
  have h3 : Entails.eval a c65 := h 64 (by decide)
  have h4 : Entails.eval a c194 := h 193 (by decide)
  have h5 : Entails.eval a c146 := h 145 (by decide)
  have h6 : Entails.eval a c135 := h 134 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c241 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨15, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f241 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c194, some c45, some c14, some c75, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p241 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked241 : lratChecker f241 p241 = .success := by decide +kernel
theorem unsat241 : Unsatisfiable (PosFin 31) f241 := by
  apply lratCheckerSound f241 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p241
  · intro a ha; simp [p241] at ha; subst a; trivial
  · exact checked241
theorem derived241 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c241 := by
  apply localUnsat_implies_entails f241 [c194, c45, c14, c75] c241 unsat241 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c45 := h 44 (by decide)
  have h2 : Entails.eval a c14 := h 13 (by decide)
  have h3 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c242 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨3, by decide⟩, true), (⟨23, by decide⟩, true), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f242 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c241, some c94, some c115, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p242 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked242 : lratChecker f242 p242 = .success := by decide +kernel
theorem unsat242 : Unsatisfiable (PosFin 31) f242 := by
  apply lratCheckerSound f242 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p242
  · intro a ha; simp [p242] at ha; subst a; trivial
  · exact checked242
theorem derived242 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c242 := by
  apply localUnsat_implies_entails f242 [c239, c241, c94, c115] c242 unsat242 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c241 := derived241 a h
  have h2 : Entails.eval a c94 := h 93 (by decide)
  have h3 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c243 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f243 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c238, some c240, some c194, some c135, some c242, some c10, some c90, some c3, some c128, some c177, some c160, some c173, some c197, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p243 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked243 : lratChecker f243 p243 = .success := by decide +kernel
theorem unsat243 : Unsatisfiable (PosFin 31) f243 := by
  apply lratCheckerSound f243 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p243
  · intro a ha; simp [p243] at ha; subst a; trivial
  · exact checked243
theorem derived243 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c243 := by
  apply localUnsat_implies_entails f243 [c239, c238, c240, c194, c135, c242, c10, c90, c3, c128, c177, c160, c173, c197] c243 unsat243 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c238 := derived238 a h
  have h2 : Entails.eval a c240 := derived240 a h
  have h3 : Entails.eval a c194 := h 193 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c242 := derived242 a h
  have h6 : Entails.eval a c10 := h 9 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  have h9 : Entails.eval a c128 := h 127 (by decide)
  have h10 : Entails.eval a c177 := h 176 (by decide)
  have h11 : Entails.eval a c160 := h 159 (by decide)
  have h12 : Entails.eval a c173 := h 172 (by decide)
  have h13 : Entails.eval a c197 := h 196 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c244 : DefaultClause 31 := directClause [(⟨11, by decide⟩, false), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f244 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c238, some c240, some c243, some c157, some c91, some c139, some c50, some c46, some c51, some c49, some c19, some c21, some c147, some c27, some c125, some c155, some c193, some c57, some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p244 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked244 : lratChecker f244 p244 = .success := by decide +kernel
theorem unsat244 : Unsatisfiable (PosFin 31) f244 := by
  apply lratCheckerSound f244 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p244
  · intro a ha; simp [p244] at ha; subst a; trivial
  · exact checked244
theorem derived244 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c244 := by
  apply localUnsat_implies_entails f244 [c239, c238, c240, c243, c157, c91, c139, c50, c46, c51, c49, c19, c21, c147, c27, c125, c155, c193, c57] c244 unsat244 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c238 := derived238 a h
  have h2 : Entails.eval a c240 := derived240 a h
  have h3 : Entails.eval a c243 := derived243 a h
  have h4 : Entails.eval a c157 := h 156 (by decide)
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c50 := h 49 (by decide)
  have h8 : Entails.eval a c46 := h 45 (by decide)
  have h9 : Entails.eval a c51 := h 50 (by decide)
  have h10 : Entails.eval a c49 := h 48 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c21 := h 20 (by decide)
  have h13 : Entails.eval a c147 := h 146 (by decide)
  have h14 : Entails.eval a c27 := h 26 (by decide)
  have h15 : Entails.eval a c125 := h 124 (by decide)
  have h16 : Entails.eval a c155 := h 154 (by decide)
  have h17 : Entails.eval a c193 := h 192 (by decide)
  have h18 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c245 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f245 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c46, some c163, some c36, some c167, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p245 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked245 : lratChecker f245 p245 = .success := by decide +kernel
theorem unsat245 : Unsatisfiable (PosFin 31) f245 := by
  apply lratCheckerSound f245 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p245
  · intro a ha; simp [p245] at ha; subst a; trivial
  · exact checked245
theorem derived245 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c245 := by
  apply localUnsat_implies_entails f245 [c238, c46, c163, c36, c167] c245 unsat245 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c46 := h 45 (by decide)
  have h2 : Entails.eval a c163 := h 162 (by decide)
  have h3 : Entails.eval a c36 := h 35 (by decide)
  have h4 : Entails.eval a c167 := h 166 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c246 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨27, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f246 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c43, some c139, some c245, some c55, some c99, some c18, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p246 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked246 : lratChecker f246 p246 = .success := by decide +kernel
theorem unsat246 : Unsatisfiable (PosFin 31) f246 := by
  apply lratCheckerSound f246 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p246
  · intro a ha; simp [p246] at ha; subst a; trivial
  · exact checked246
theorem derived246 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c246 := by
  apply localUnsat_implies_entails f246 [c239, c43, c139, c245, c55, c99, c18] c246 unsat246 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c43 := h 42 (by decide)
  have h2 : Entails.eval a c139 := h 138 (by decide)
  have h3 : Entails.eval a c245 := derived245 a h
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c99 := h 98 (by decide)
  have h6 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c247 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨15, by decide⟩, false), (⟨11, by decide⟩, true), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f247 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c61, some c55, some c35, some c18, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p247 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked247 : lratChecker f247 p247 = .success := by decide +kernel
theorem unsat247 : Unsatisfiable (PosFin 31) f247 := by
  apply lratCheckerSound f247 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p247
  · intro a ha; simp [p247] at ha; subst a; trivial
  · exact checked247
theorem derived247 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c247 := by
  apply localUnsat_implies_entails f247 [c239, c61, c55, c35, c18] c247 unsat247 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c248 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f248 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c239, some c244, some c43, some c5, some c88, some c246, some c17, some c247, some c46, some c163, some c36, some c189, some c192, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p248 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked248 : lratChecker f248 p248 = .success := by decide +kernel
theorem unsat248 : Unsatisfiable (PosFin 31) f248 := by
  apply lratCheckerSound f248 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p248
  · intro a ha; simp [p248] at ha; subst a; trivial
  · exact checked248
theorem derived248 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c248 := by
  apply localUnsat_implies_entails f248 [c238, c239, c244, c43, c5, c88, c246, c17, c247, c46, c163, c36, c189, c192] c248 unsat248 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c239 := derived239 a h
  have h2 : Entails.eval a c244 := derived244 a h
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c88 := h 87 (by decide)
  have h6 : Entails.eval a c246 := derived246 a h
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c247 := derived247 a h
  have h9 : Entails.eval a c46 := h 45 (by decide)
  have h10 : Entails.eval a c163 := h 162 (by decide)
  have h11 : Entails.eval a c36 := h 35 (by decide)
  have h12 : Entails.eval a c189 := h 188 (by decide)
  have h13 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c249 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, true), (⟨1, by decide⟩, true), (⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨21, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f249 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c239, some c46, some c163, some c36, some c189, some c192, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, false))]
def p249 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked249 : lratChecker f249 p249 = .success := by decide +kernel
theorem unsat249 : Unsatisfiable (PosFin 31) f249 := by
  apply lratCheckerSound f249 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p249
  · intro a ha; simp [p249] at ha; subst a; trivial
  · exact checked249
theorem derived249 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c249 := by
  apply localUnsat_implies_entails f249 [c238, c239, c46, c163, c36, c189, c192] c249 unsat249 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c239 := derived239 a h
  have h2 : Entails.eval a c46 := h 45 (by decide)
  have h3 : Entails.eval a c163 := h 162 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c250 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f250 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c244, some c43, some c5, some c248, some c91, some c40, some c17, some c137, some c249, some c113, some c55, some c140, some c92, some c18, some c138, some c161, some c109, some c191, some c57, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p250 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked250 : lratChecker f250 p250 = .success := by decide +kernel
theorem unsat250 : Unsatisfiable (PosFin 31) f250 := by
  apply lratCheckerSound f250 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p250
  · intro a ha; simp [p250] at ha; subst a; trivial
  · exact checked250
theorem derived250 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c250 := by
  apply localUnsat_implies_entails f250 [c239, c244, c43, c5, c248, c91, c40, c17, c137, c249, c113, c55, c140, c92, c18, c138, c161, c109, c191, c57] c250 unsat250 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c244 := derived244 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c248 := derived248 a h
  have h5 : Entails.eval a c91 := h 90 (by decide)
  have h6 : Entails.eval a c40 := h 39 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c137 := h 136 (by decide)
  have h9 : Entails.eval a c249 := derived249 a h
  have h10 : Entails.eval a c113 := h 112 (by decide)
  have h11 : Entails.eval a c55 := h 54 (by decide)
  have h12 : Entails.eval a c140 := h 139 (by decide)
  have h13 : Entails.eval a c92 := h 91 (by decide)
  have h14 : Entails.eval a c18 := h 17 (by decide)
  have h15 : Entails.eval a c138 := h 137 (by decide)
  have h16 : Entails.eval a c161 := h 160 (by decide)
  have h17 : Entails.eval a c109 := h 108 (by decide)
  have h18 : Entails.eval a c191 := h 190 (by decide)
  have h19 : Entails.eval a c57 := h 56 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c251 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f251 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c244, some c43, some c5, some c250, some c194, some c45, some c128, some c126, some c61, some c138, some c161, some c60, some c185, some c137, some c169, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p251 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked251 : lratChecker f251 p251 = .success := by decide +kernel
theorem unsat251 : Unsatisfiable (PosFin 31) f251 := by
  apply lratCheckerSound f251 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p251
  · intro a ha; simp [p251] at ha; subst a; trivial
  · exact checked251
theorem derived251 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c251 := by
  apply localUnsat_implies_entails f251 [c239, c244, c43, c5, c250, c194, c45, c128, c126, c61, c138, c161, c60, c185, c137, c169] c251 unsat251 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c244 := derived244 a h
  have h2 : Entails.eval a c43 := h 42 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c250 := derived250 a h
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c45 := h 44 (by decide)
  have h7 : Entails.eval a c128 := h 127 (by decide)
  have h8 : Entails.eval a c126 := h 125 (by decide)
  have h9 : Entails.eval a c61 := h 60 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c60 := h 59 (by decide)
  have h13 : Entails.eval a c185 := h 184 (by decide)
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c252 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f252 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c244, some c5, some c43, some c251, some c53, some c158, some c52, some c88, some c172, some c138, some c161, some c36, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p252 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked252 : lratChecker f252 p252 = .success := by decide +kernel
theorem unsat252 : Unsatisfiable (PosFin 31) f252 := by
  apply lratCheckerSound f252 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p252
  · intro a ha; simp [p252] at ha; subst a; trivial
  · exact checked252
theorem derived252 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c252 := by
  apply localUnsat_implies_entails f252 [c239, c244, c5, c43, c251, c53, c158, c52, c88, c172, c138, c161, c36] c252 unsat252 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c244 := derived244 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  have h4 : Entails.eval a c251 := derived251 a h
  have h5 : Entails.eval a c53 := h 52 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  have h7 : Entails.eval a c52 := h 51 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c172 := h 171 (by decide)
  have h10 : Entails.eval a c138 := h 137 (by decide)
  have h11 : Entails.eval a c161 := h 160 (by decide)
  have h12 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c253 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨12, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f253 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c252, some c54, some c158, some c4, some c92, some c161, some c194, some c13, some c85, some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p253 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked253 : lratChecker f253 p253 = .success := by decide +kernel
theorem unsat253 : Unsatisfiable (PosFin 31) f253 := by
  apply lratCheckerSound f253 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p253
  · intro a ha; simp [p253] at ha; subst a; trivial
  · exact checked253
theorem derived253 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c253 := by
  apply localUnsat_implies_entails f253 [c239, c252, c54, c158, c4, c92, c161, c194, c13, c85] c253 unsat253 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c54 := h 53 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c4 := h 3 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c161 := h 160 (by decide)
  have h7 : Entails.eval a c194 := h 193 (by decide)
  have h8 : Entails.eval a c13 := h 12 (by decide)
  have h9 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c254 : DefaultClause 31 := directClause [(⟨3, by decide⟩, false), (⟨6, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f254 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c85, some c112, some c194, some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p254 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked254 : lratChecker f254 p254 = .success := by decide +kernel
theorem unsat254 : Unsatisfiable (PosFin 31) f254 := by
  apply lratCheckerSound f254 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p254
  · intro a ha; simp [p254] at ha; subst a; trivial
  · exact checked254
theorem derived254 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c254 := by
  apply localUnsat_implies_entails f254 [c85, c112, c194] c254 unsat254 (by rfl) a
  have h0 : Entails.eval a c85 := h 84 (by decide)
  have h1 : Entails.eval a c112 := h 111 (by decide)
  have h2 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c255 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f255 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c252, some c254, some c54, some c156, some c158, some c253, some c9, some c115, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p255 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked255 : lratChecker f255 p255 = .success := by decide +kernel
theorem unsat255 : Unsatisfiable (PosFin 31) f255 := by
  apply lratCheckerSound f255 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p255
  · intro a ha; simp [p255] at ha; subst a; trivial
  · exact checked255
theorem derived255 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c255 := by
  apply localUnsat_implies_entails f255 [c239, c252, c254, c54, c156, c158, c253, c9, c115] c255 unsat255 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c254 := derived254 a h
  have h3 : Entails.eval a c54 := h 53 (by decide)
  have h4 : Entails.eval a c156 := h 155 (by decide)
  have h5 : Entails.eval a c158 := h 157 (by decide)
  have h6 : Entails.eval a c253 := derived253 a h
  have h7 : Entails.eval a c9 := h 8 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c256 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨11, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f256 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c252, some c254, some c141, some c115, some c160, some c3, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p256 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked256 : lratChecker f256 p256 = .success := by decide +kernel
theorem unsat256 : Unsatisfiable (PosFin 31) f256 := by
  apply lratCheckerSound f256 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p256
  · intro a ha; simp [p256] at ha; subst a; trivial
  · exact checked256
theorem derived256 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c256 := by
  apply localUnsat_implies_entails f256 [c239, c252, c254, c141, c115, c160, c3] c256 unsat256 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c254 := derived254 a h
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c115 := h 114 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c257 : DefaultClause 31 := directClause [(⟨21, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f257 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c255, some c252, some c254, some c100, some c45, some c245, some c91, some c64, some c224, some c46, some c81, some c58, some c153, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p257 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked257 : lratChecker f257 p257 = .success := by decide +kernel
theorem unsat257 : Unsatisfiable (PosFin 31) f257 := by
  apply lratCheckerSound f257 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p257
  · intro a ha; simp [p257] at ha; subst a; trivial
  · exact checked257
theorem derived257 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c257 := by
  apply localUnsat_implies_entails f257 [c239, c255, c252, c254, c100, c45, c245, c91, c64, c224, c46, c81, c58, c153] c257 unsat257 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c255 := derived255 a h
  have h2 : Entails.eval a c252 := derived252 a h
  have h3 : Entails.eval a c254 := derived254 a h
  have h4 : Entails.eval a c100 := h 99 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c245 := derived245 a h
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c64 := h 63 (by decide)
  have h9 : Entails.eval a c224 := derived224 a h
  have h10 : Entails.eval a c46 := h 45 (by decide)
  have h11 : Entails.eval a c81 := h 80 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c258 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f258 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c252, some c254, some c111, some c257, some c256, some c37, some c255, some c107, some c11, some c89, some c51, some c34, some c59, some c19, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p258 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked258 : lratChecker f258 p258 = .success := by decide +kernel
theorem unsat258 : Unsatisfiable (PosFin 31) f258 := by
  apply lratCheckerSound f258 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p258
  · intro a ha; simp [p258] at ha; subst a; trivial
  · exact checked258
theorem derived258 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c258 := by
  apply localUnsat_implies_entails f258 [c239, c252, c254, c111, c257, c256, c37, c255, c107, c11, c89, c51, c34, c59, c19] c258 unsat258 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c252 := derived252 a h
  have h2 : Entails.eval a c254 := derived254 a h
  have h3 : Entails.eval a c111 := h 110 (by decide)
  have h4 : Entails.eval a c257 := derived257 a h
  have h5 : Entails.eval a c256 := derived256 a h
  have h6 : Entails.eval a c37 := h 36 (by decide)
  have h7 : Entails.eval a c255 := derived255 a h
  have h8 : Entails.eval a c107 := h 106 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c89 := h 88 (by decide)
  have h11 : Entails.eval a c51 := h 50 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c59 := h 58 (by decide)
  have h14 : Entails.eval a c19 := h 18 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c259 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f259 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c257, some c37, some c252, some c254, some c258, some c91, some c3, some c11, some c154, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p259 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked259 : lratChecker f259 p259 = .success := by decide +kernel
theorem unsat259 : Unsatisfiable (PosFin 31) f259 := by
  apply lratCheckerSound f259 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p259
  · intro a ha; simp [p259] at ha; subst a; trivial
  · exact checked259
theorem derived259 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c259 := by
  apply localUnsat_implies_entails f259 [c239, c257, c37, c252, c254, c258, c91, c3, c11, c154] c259 unsat259 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c257 := derived257 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c252 := derived252 a h
  have h4 : Entails.eval a c254 := derived254 a h
  have h5 : Entails.eval a c258 := derived258 a h
  have h6 : Entails.eval a c91 := h 90 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c11 := h 10 (by decide)
  have h9 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c260 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f260 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c254, some c257, some c259, some c115, some c160, some c3, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p260 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked260 : lratChecker f260 p260 = .success := by decide +kernel
theorem unsat260 : Unsatisfiable (PosFin 31) f260 := by
  apply lratCheckerSound f260 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p260
  · intro a ha; simp [p260] at ha; subst a; trivial
  · exact checked260
theorem derived260 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c260 := by
  apply localUnsat_implies_entails f260 [c254, c257, c259, c115, c160, c3] c260 unsat260 (by rfl) a
  have h0 : Entails.eval a c254 := derived254 a h
  have h1 : Entails.eval a c257 := derived257 a h
  have h2 : Entails.eval a c259 := derived259 a h
  have h3 : Entails.eval a c115 := h 114 (by decide)
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c261 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f261 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c252, some c260, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p261 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked261 : lratChecker f261 p261 = .success := by decide +kernel
theorem unsat261 : Unsatisfiable (PosFin 31) f261 := by
  apply lratCheckerSound f261 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p261
  · intro a ha; simp [p261] at ha; subst a; trivial
  · exact checked261
theorem derived261 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c261 := by
  apply localUnsat_implies_entails f261 [c252, c260] c261 unsat261 (by rfl) a
  have h0 : Entails.eval a c252 := derived252 a h
  have h1 : Entails.eval a c260 := derived260 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c262 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f262 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c261, some c22, some c6, some c55, some c48, some c39, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p262 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked262 : lratChecker f262 p262 = .success := by decide +kernel
theorem unsat262 : Unsatisfiable (PosFin 31) f262 := by
  apply lratCheckerSound f262 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p262
  · intro a ha; simp [p262] at ha; subst a; trivial
  · exact checked262
theorem derived262 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c262 := by
  apply localUnsat_implies_entails f262 [c239, c261, c22, c6, c55, c48, c39] c262 unsat262 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c22 := h 21 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c55 := h 54 (by decide)
  have h5 : Entails.eval a c48 := h 47 (by decide)
  have h6 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c263 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f263 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c238, some c239, some c37, some c177, some c164, some c196, some c169, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p263 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked263 : lratChecker f263 p263 = .success := by decide +kernel
theorem unsat263 : Unsatisfiable (PosFin 31) f263 := by
  apply lratCheckerSound f263 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p263
  · intro a ha; simp [p263] at ha; subst a; trivial
  · exact checked263
theorem derived263 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c263 := by
  apply localUnsat_implies_entails f263 [c238, c239, c37, c177, c164, c196, c169] c263 unsat263 (by rfl) a
  have h0 : Entails.eval a c238 := derived238 a h
  have h1 : Entails.eval a c239 := derived239 a h
  have h2 : Entails.eval a c37 := h 36 (by decide)
  have h3 : Entails.eval a c177 := h 176 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  have h5 : Entails.eval a c196 := h 195 (by decide)
  have h6 : Entails.eval a c169 := h 168 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c264 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f264 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c56, some c52, some c39, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p264 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked264 : lratChecker f264 p264 = .success := by decide +kernel
theorem unsat264 : Unsatisfiable (PosFin 31) f264 := by
  apply lratCheckerSound f264 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p264
  · intro a ha; simp [p264] at ha; subst a; trivial
  · exact checked264
theorem derived264 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c264 := by
  apply localUnsat_implies_entails f264 [c239, c56, c52, c39] c264 unsat264 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c56 := h 55 (by decide)
  have h2 : Entails.eval a c52 := h 51 (by decide)
  have h3 : Entails.eval a c39 := h 38 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c265 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f265 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c261, some c239, some c29, some c6, some c264, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p265 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked265 : lratChecker f265 p265 = .success := by decide +kernel
theorem unsat265 : Unsatisfiable (PosFin 31) f265 := by
  apply lratCheckerSound f265 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p265
  · intro a ha; simp [p265] at ha; subst a; trivial
  · exact checked265
theorem derived265 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c265 := by
  apply localUnsat_implies_entails f265 [c261, c239, c29, c6, c264] c265 unsat265 (by rfl) a
  have h0 : Entails.eval a c261 := derived261 a h
  have h1 : Entails.eval a c239 := derived239 a h
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c264 := derived264 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c266 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f266 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c262, some c263, some c40, some c265, some (DefaultClause.unit (⟨21, by decide⟩, true))]
def p266 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked266 : lratChecker f266 p266 = .success := by decide +kernel
theorem unsat266 : Unsatisfiable (PosFin 31) f266 := by
  apply lratCheckerSound f266 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p266
  · intro a ha; simp [p266] at ha; subst a; trivial
  · exact checked266
theorem derived266 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c266 := by
  apply localUnsat_implies_entails f266 [c239, c262, c263, c40, c265] c266 unsat266 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c262 := derived262 a h
  have h2 : Entails.eval a c263 := derived263 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  have h4 : Entails.eval a c265 := derived265 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c267 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨13, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f267 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c261, some c238, some c239, some c96, some c23, some c97, some c163, some c179, some c170, some c71, some c180, some c120, some c152, some c127, some c139, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p267 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked267 : lratChecker f267 p267 = .success := by decide +kernel
theorem unsat267 : Unsatisfiable (PosFin 31) f267 := by
  apply lratCheckerSound f267 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p267
  · intro a ha; simp [p267] at ha; subst a; trivial
  · exact checked267
theorem derived267 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c267 := by
  apply localUnsat_implies_entails f267 [c266, c261, c238, c239, c96, c23, c97, c163, c179, c170, c71, c180, c120, c152, c127, c139] c267 unsat267 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c238 := derived238 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c96 := h 95 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c97 := h 96 (by decide)
  have h7 : Entails.eval a c163 := h 162 (by decide)
  have h8 : Entails.eval a c179 := h 178 (by decide)
  have h9 : Entails.eval a c170 := h 169 (by decide)
  have h10 : Entails.eval a c71 := h 70 (by decide)
  have h11 : Entails.eval a c180 := h 179 (by decide)
  have h12 : Entails.eval a c120 := h 119 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  have h14 : Entails.eval a c127 := h 126 (by decide)
  have h15 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c268 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true), (⟨18, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f268 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c194, some c101, some c75, some (DefaultClause.unit (⟨23, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p268 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked268 : lratChecker f268 p268 = .success := by decide +kernel
theorem unsat268 : Unsatisfiable (PosFin 31) f268 := by
  apply lratCheckerSound f268 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p268
  · intro a ha; simp [p268] at ha; subst a; trivial
  · exact checked268
theorem derived268 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c268 := by
  apply localUnsat_implies_entails f268 [c194, c101, c75] c268 unsat268 (by rfl) a
  have h0 : Entails.eval a c194 := h 193 (by decide)
  have h1 : Entails.eval a c101 := h 100 (by decide)
  have h2 : Entails.eval a c75 := h 74 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c269 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f269 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c52, some c267, some c268, some c23, some c30, some c247, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p269 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked269 : lratChecker f269 p269 = .success := by decide +kernel
theorem unsat269 : Unsatisfiable (PosFin 31) f269 := by
  apply lratCheckerSound f269 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p269
  · intro a ha; simp [p269] at ha; subst a; trivial
  · exact checked269
theorem derived269 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c269 := by
  apply localUnsat_implies_entails f269 [c239, c52, c267, c268, c23, c30, c247] c269 unsat269 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c52 := h 51 (by decide)
  have h2 : Entails.eval a c267 := derived267 a h
  have h3 : Entails.eval a c268 := derived268 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c30 := h 29 (by decide)
  have h6 : Entails.eval a c247 := derived247 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c270 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨15, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f270 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c239, some c50, some c30, some c247, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p270 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked270 : lratChecker f270 p270 = .success := by decide +kernel
theorem unsat270 : Unsatisfiable (PosFin 31) f270 := by
  apply lratCheckerSound f270 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p270
  · intro a ha; simp [p270] at ha; subst a; trivial
  · exact checked270
theorem derived270 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c270 := by
  apply localUnsat_implies_entails f270 [c239, c50, c30, c247] c270 unsat270 (by rfl) a
  have h0 : Entails.eval a c239 := derived239 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c30 := h 29 (by decide)
  have h3 : Entails.eval a c247 := derived247 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c271 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f271 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c266, some c261, some c269, some c6, some c143, some c270, some (DefaultClause.unit (⟨15, by decide⟩, true))]
def p271 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked271 : lratChecker f271 p271 = .success := by decide +kernel
theorem unsat271 : Unsatisfiable (PosFin 31) f271 := by
  apply lratCheckerSound f271 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p271
  · intro a ha; simp [p271] at ha; subst a; trivial
  · exact checked271
theorem derived271 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c271 := by
  apply localUnsat_implies_entails f271 [c266, c261, c269, c6, c143, c270] c271 unsat271 (by rfl) a
  have h0 : Entails.eval a c266 := derived266 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c269 := derived269 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c143 := h 142 (by decide)
  have h5 : Entails.eval a c270 := derived270 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c272 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f272 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c261, some c238, some c266, some c271, some c239, some c40, some c30, some c91, some c55, some c53, some c106, some c215, some c163, some c171, some c190, some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p272 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked272 : lratChecker f272 p272 = .success := by decide +kernel
theorem unsat272 : Unsatisfiable (PosFin 31) f272 := by
  apply lratCheckerSound f272 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p272
  · intro a ha; simp [p272] at ha; subst a; trivial
  · exact checked272
theorem derived272 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c272 := by
  apply localUnsat_implies_entails f272 [c261, c238, c266, c271, c239, c40, c30, c91, c55, c53, c106, c215, c163, c171, c190] c272 unsat272 (by rfl) a
  have h0 : Entails.eval a c261 := derived261 a h
  have h1 : Entails.eval a c238 := derived238 a h
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c271 := derived271 a h
  have h4 : Entails.eval a c239 := derived239 a h
  have h5 : Entails.eval a c40 := h 39 (by decide)
  have h6 : Entails.eval a c30 := h 29 (by decide)
  have h7 : Entails.eval a c91 := h 90 (by decide)
  have h8 : Entails.eval a c55 := h 54 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  have h10 : Entails.eval a c106 := h 105 (by decide)
  have h11 : Entails.eval a c215 := derived215 a h
  have h12 : Entails.eval a c163 := h 162 (by decide)
  have h13 : Entails.eval a c171 := h 170 (by decide)
  have h14 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c273 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f273 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c271, some c261, some c266, some c239, some c272, some c194, some c143, some c231, some c87, some c54, some c100, some c113, some c82, some c74, some c152, some c72, some c175, some c165, some c148, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p273 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]]
theorem checked273 : lratChecker f273 p273 = .success := by decide +kernel
theorem unsat273 : Unsatisfiable (PosFin 31) f273 := by
  apply lratCheckerSound f273 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p273
  · intro a ha; simp [p273] at ha; subst a; trivial
  · exact checked273
theorem derived273 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c273 := by
  apply localUnsat_implies_entails f273 [c271, c261, c266, c239, c272, c194, c143, c231, c87, c54, c100, c113, c82, c74, c152, c72, c175, c165, c148] c273 unsat273 (by rfl) a
  have h0 : Entails.eval a c271 := derived271 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c239 := derived239 a h
  have h4 : Entails.eval a c272 := derived272 a h
  have h5 : Entails.eval a c194 := h 193 (by decide)
  have h6 : Entails.eval a c143 := h 142 (by decide)
  have h7 : Entails.eval a c231 := derived231 a h
  have h8 : Entails.eval a c87 := h 86 (by decide)
  have h9 : Entails.eval a c54 := h 53 (by decide)
  have h10 : Entails.eval a c100 := h 99 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c82 := h 81 (by decide)
  have h13 : Entails.eval a c74 := h 73 (by decide)
  have h14 : Entails.eval a c152 := h 151 (by decide)
  have h15 : Entails.eval a c72 := h 71 (by decide)
  have h16 : Entails.eval a c175 := h 174 (by decide)
  have h17 : Entails.eval a c165 := h 164 (by decide)
  have h18 : Entails.eval a c148 := h 147 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c274 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f274 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c273, some c261, some c6, some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p274 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked274 : lratChecker f274 p274 = .success := by decide +kernel
theorem unsat274 : Unsatisfiable (PosFin 31) f274 := by
  apply lratCheckerSound f274 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p274
  · intro a ha; simp [p274] at ha; subst a; trivial
  · exact checked274
theorem derived274 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c274 := by
  apply localUnsat_implies_entails f274 [c273, c261, c6] c274 unsat274 (by rfl) a
  have h0 : Entails.eval a c273 := derived273 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c6 := h 5 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c275 : DefaultClause 31 := directClause [(⟨23, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f275 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c273, some c261, some c266, some c96, some (DefaultClause.unit (⟨23, by decide⟩, false))]
def p275 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked275 : lratChecker f275 p275 = .success := by decide +kernel
theorem unsat275 : Unsatisfiable (PosFin 31) f275 := by
  apply lratCheckerSound f275 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p275
  · intro a ha; simp [p275] at ha; subst a; trivial
  · exact checked275
theorem derived275 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c275 := by
  apply localUnsat_implies_entails f275 [c273, c261, c266, c96] c275 unsat275 (by rfl) a
  have h0 : Entails.eval a c273 := derived273 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c266 := derived266 a h
  have h3 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c276 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f276 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c274, some c261, some c271, some c231, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p276 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked276 : lratChecker f276 p276 = .success := by decide +kernel
theorem unsat276 : Unsatisfiable (PosFin 31) f276 := by
  apply lratCheckerSound f276 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p276
  · intro a ha; simp [p276] at ha; subst a; trivial
  · exact checked276
theorem derived276 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c276 := by
  apply localUnsat_implies_entails f276 [c274, c261, c271, c231] c276 unsat276 (by rfl) a
  have h0 : Entails.eval a c274 := derived274 a h
  have h1 : Entails.eval a c261 := derived261 a h
  have h2 : Entails.eval a c271 := derived271 a h
  have h3 : Entails.eval a c231 := derived231 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c277 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f277 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c275, some c271, some c239, some c40, some (DefaultClause.unit (⟨9, by decide⟩, false))]
def p277 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked277 : lratChecker f277 p277 = .success := by decide +kernel
theorem unsat277 : Unsatisfiable (PosFin 31) f277 := by
  apply lratCheckerSound f277 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p277
  · intro a ha; simp [p277] at ha; subst a; trivial
  · exact checked277
theorem derived277 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c277 := by
  apply localUnsat_implies_entails f277 [c275, c271, c239, c40] c277 unsat277 (by rfl) a
  have h0 : Entails.eval a c275 := derived275 a h
  have h1 : Entails.eval a c271 := derived271 a h
  have h2 : Entails.eval a c239 := derived239 a h
  have h3 : Entails.eval a c40 := h 39 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c278 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f278 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c277, some c276, some c275, some c274, some c62]
def p278 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked278 : lratChecker f278 p278 = .success := by decide +kernel
theorem unsat278 : Unsatisfiable (PosFin 31) f278 := by
  apply lratCheckerSound f278 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p278
  · intro a ha; simp [p278] at ha; subst a; trivial
  · exact checked278
theorem derived278 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c278 := by
  apply localUnsat_implies_entails f278 [c277, c276, c275, c274, c62] c278 unsat278 (by rfl) a
  have h0 : Entails.eval a c277 := derived277 a h
  have h1 : Entails.eval a c276 := derived276 a h
  have h2 : Entails.eval a c275 := derived275 a h
  have h3 : Entails.eval a c274 := derived274 a h
  have h4 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived278

end CochromaticTwenty.Certificates.Z12Direct_5_3_0
