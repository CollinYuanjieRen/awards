import MerLeanExperiment.Certificates.Z12Direct_5_5_6.Inputs

/-! Generated from the actual pinned z12direct_5_5_6-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_5_6
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c165 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f165 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c16, some c17, some c20, some c81, some c41, some c10, some c134, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p165 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked165 : lratChecker f165 p165 = .success := by decide +kernel
theorem unsat165 : Unsatisfiable (PosFin 31) f165 := by
  apply lratCheckerSound f165 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p165
  · intro a ha; simp [p165] at ha; subst a; trivial
  · exact checked165
theorem derived165 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c165 := by
  apply localUnsat_implies_entails f165 [c16, c17, c20, c81, c41, c10, c134] c165 unsat165 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c20 := h 19 (by decide)
  have h3 : Entails.eval a c81 := h 80 (by decide)
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c134 := h 133 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c166 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨27, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f166 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c165, some c29, some c88, some c11, some c12, some c139, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p166 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked166 : lratChecker f166 p166 = .success := by decide +kernel
theorem unsat166 : Unsatisfiable (PosFin 31) f166 := by
  apply lratCheckerSound f166 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p166
  · intro a ha; simp [p166] at ha; subst a; trivial
  · exact checked166
theorem derived166 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c166 := by
  apply localUnsat_implies_entails f166 [c165, c29, c88, c11, c12, c139] c166 unsat166 (by rfl) a
  have h0 : Entails.eval a c165 := derived165 a h
  have h1 : Entails.eval a c29 := h 28 (by decide)
  have h2 : Entails.eval a c88 := h 87 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c12 := h 11 (by decide)
  have h5 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c167 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f167 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c30, some c89, some c12, some c7, some c126, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p167 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked167 : lratChecker f167 p167 = .success := by decide +kernel
theorem unsat167 : Unsatisfiable (PosFin 31) f167 := by
  apply lratCheckerSound f167 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p167
  · intro a ha; simp [p167] at ha; subst a; trivial
  · exact checked167
theorem derived167 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c167 := by
  apply localUnsat_implies_entails f167 [c30, c89, c12, c7, c126] c167 unsat167 (by rfl) a
  have h0 : Entails.eval a c30 := h 29 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c126 := h 125 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c168 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨28, by decide⟩, false), (⟨30, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f168 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c167, some c17, some c23, some c82, some c50, some c12, some c136, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p168 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked168 : lratChecker f168 p168 = .success := by decide +kernel
theorem unsat168 : Unsatisfiable (PosFin 31) f168 := by
  apply lratCheckerSound f168 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p168
  · intro a ha; simp [p168] at ha; subst a; trivial
  · exact checked168
theorem derived168 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c168 := by
  apply localUnsat_implies_entails f168 [c167, c17, c23, c82, c50, c12, c136] c168 unsat168 (by rfl) a
  have h0 : Entails.eval a c167 := derived167 a h
  have h1 : Entails.eval a c17 := h 16 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c50 := h 49 (by decide)
  have h5 : Entails.eval a c12 := h 11 (by decide)
  have h6 : Entails.eval a c136 := h 135 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c169 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true), (⟨12, by decide⟩, true), (⟨21, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f169 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c79, some c149, some c82, some (DefaultClause.unit (⟨10, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p169 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked169 : lratChecker f169 p169 = .success := by decide +kernel
theorem unsat169 : Unsatisfiable (PosFin 31) f169 := by
  apply lratCheckerSound f169 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p169
  · intro a ha; simp [p169] at ha; subst a; trivial
  · exact checked169
theorem derived169 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c169 := by
  apply localUnsat_implies_entails f169 [c79, c149, c82] c169 unsat169 (by rfl) a
  have h0 : Entails.eval a c79 := h 78 (by decide)
  have h1 : Entails.eval a c149 := h 148 (by decide)
  have h2 : Entails.eval a c82 := h 81 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c170 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f170 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c50, some c38, some c23, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p170 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked170 : lratChecker f170 p170 = .success := by decide +kernel
theorem unsat170 : Unsatisfiable (PosFin 31) f170 := by
  apply lratCheckerSound f170 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p170
  · intro a ha; simp [p170] at ha; subst a; trivial
  · exact checked170
theorem derived170 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c170 := by
  apply localUnsat_implies_entails f170 [c50, c38, c23] c170 unsat170 (by rfl) a
  have h0 : Entails.eval a c50 := h 49 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c171 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f171 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c160, some c170, some c169, some c23, some c44, some c73, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p171 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked171 : lratChecker f171 p171 = .success := by decide +kernel
theorem unsat171 : Unsatisfiable (PosFin 31) f171 := by
  apply lratCheckerSound f171 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p171
  · intro a ha; simp [p171] at ha; subst a; trivial
  · exact checked171
theorem derived171 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c171 := by
  apply localUnsat_implies_entails f171 [c168, c160, c170, c169, c23, c44, c73] c171 unsat171 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c170 := derived170 a h
  have h3 : Entails.eval a c169 := derived169 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c44 := h 43 (by decide)
  have h6 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c172 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f172 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c160, some c170, some c169, some c171, some c137, some c52, some c3, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p172 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked172 : lratChecker f172 p172 = .success := by decide +kernel
theorem unsat172 : Unsatisfiable (PosFin 31) f172 := by
  apply lratCheckerSound f172 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p172
  · intro a ha; simp [p172] at ha; subst a; trivial
  · exact checked172
theorem derived172 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c172 := by
  apply localUnsat_implies_entails f172 [c168, c160, c170, c169, c171, c137, c52, c3] c172 unsat172 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c170 := derived170 a h
  have h3 : Entails.eval a c169 := derived169 a h
  have h4 : Entails.eval a c171 := derived171 a h
  have h5 : Entails.eval a c137 := h 136 (by decide)
  have h6 : Entails.eval a c52 := h 51 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c173 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨21, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f173 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c65, some c52, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p173 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked173 : lratChecker f173 p173 = .success := by decide +kernel
theorem unsat173 : Unsatisfiable (PosFin 31) f173 := by
  apply lratCheckerSound f173 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p173
  · intro a ha; simp [p173] at ha; subst a; trivial
  · exact checked173
theorem derived173 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c173 := by
  apply localUnsat_implies_entails f173 [c65, c52] c173 unsat173 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c174 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f174 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c172, some c168, some c160, some c173, some c23, some c126, some c43, some c109, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p174 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked174 : lratChecker f174 p174 = .success := by decide +kernel
theorem unsat174 : Unsatisfiable (PosFin 31) f174 := by
  apply lratCheckerSound f174 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p174
  · intro a ha; simp [p174] at ha; subst a; trivial
  · exact checked174
theorem derived174 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c174 := by
  apply localUnsat_implies_entails f174 [c172, c168, c160, c173, c23, c126, c43, c109] c174 unsat174 (by rfl) a
  have h0 : Entails.eval a c172 := derived172 a h
  have h1 : Entails.eval a c168 := derived168 a h
  have h2 : Entails.eval a c160 := h 159 (by decide)
  have h3 : Entails.eval a c173 := derived173 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c126 := h 125 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c109 := h 108 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c175 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f175 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c168, some c172, some c174, some c29, some c28, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p175 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked175 : lratChecker f175 p175 = .success := by decide +kernel
theorem unsat175 : Unsatisfiable (PosFin 31) f175 := by
  apply lratCheckerSound f175 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p175
  · intro a ha; simp [p175] at ha; subst a; trivial
  · exact checked175
theorem derived175 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c175 := by
  apply localUnsat_implies_entails f175 [c168, c172, c174, c29, c28] c175 unsat175 (by rfl) a
  have h0 : Entails.eval a c168 := derived168 a h
  have h1 : Entails.eval a c172 := derived172 a h
  have h2 : Entails.eval a c174 := derived174 a h
  have h3 : Entails.eval a c29 := h 28 (by decide)
  have h4 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c176 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f176 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c29, some c28, some c5, some c7, some c175, some c159, some c61, some c59, some c139, some c2, some c140, some c64, some c98, some c150, some c96, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p176 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked176 : lratChecker f176 p176 = .success := by decide +kernel
theorem unsat176 : Unsatisfiable (PosFin 31) f176 := by
  apply lratCheckerSound f176 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p176
  · intro a ha; simp [p176] at ha; subst a; trivial
  · exact checked176
theorem derived176 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c176 := by
  apply localUnsat_implies_entails f176 [c29, c28, c5, c7, c175, c159, c61, c59, c139, c2, c140, c64, c98, c150, c96] c176 unsat176 (by rfl) a
  have h0 : Entails.eval a c29 := h 28 (by decide)
  have h1 : Entails.eval a c28 := h 27 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c175 := derived175 a h
  have h5 : Entails.eval a c159 := h 158 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c59 := h 58 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  have h9 : Entails.eval a c2 := h 1 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c64 := h 63 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c150 := h 149 (by decide)
  have h14 : Entails.eval a c96 := h 95 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c177 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f177 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c175, some c159, some c29, some c61, some c59, some c5, some c28, some c176, some c36, some c142, some c35, some c124, some c64, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p177 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked177 : lratChecker f177 p177 = .success := by decide +kernel
theorem unsat177 : Unsatisfiable (PosFin 31) f177 := by
  apply lratCheckerSound f177 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p177
  · intro a ha; simp [p177] at ha; subst a; trivial
  · exact checked177
theorem derived177 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c177 := by
  apply localUnsat_implies_entails f177 [c175, c159, c29, c61, c59, c5, c28, c176, c36, c142, c35, c124, c64] c177 unsat177 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c29 := h 28 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c5 := h 4 (by decide)
  have h6 : Entails.eval a c28 := h 27 (by decide)
  have h7 : Entails.eval a c176 := derived176 a h
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c35 := h 34 (by decide)
  have h11 : Entails.eval a c124 := h 123 (by decide)
  have h12 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c178 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨20, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f178 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c49, some c64, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p178 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked178 : lratChecker f178 p178 = .success := by decide +kernel
theorem unsat178 : Unsatisfiable (PosFin 31) f178 := by
  apply lratCheckerSound f178 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p178
  · intro a ha; simp [p178] at ha; subst a; trivial
  · exact checked178
theorem derived178 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c178 := by
  apply localUnsat_implies_entails f178 [c49, c64] c178 unsat178 (by rfl) a
  have h0 : Entails.eval a c49 := h 48 (by decide)
  have h1 : Entails.eval a c64 := h 63 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c179 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f179 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c177, some c166, some c12, some c162, some c178, some c20, some c139, some c124, some c123, some c141, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p179 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked179 : lratChecker f179 p179 = .success := by decide +kernel
theorem unsat179 : Unsatisfiable (PosFin 31) f179 := by
  apply lratCheckerSound f179 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p179
  · intro a ha; simp [p179] at ha; subst a; trivial
  · exact checked179
theorem derived179 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c179 := by
  apply localUnsat_implies_entails f179 [c177, c166, c12, c162, c178, c20, c139, c124, c123, c141] c179 unsat179 (by rfl) a
  have h0 : Entails.eval a c177 := derived177 a h
  have h1 : Entails.eval a c166 := derived166 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c178 := derived178 a h
  have h5 : Entails.eval a c20 := h 19 (by decide)
  have h6 : Entails.eval a c139 := h 138 (by decide)
  have h7 : Entails.eval a c124 := h 123 (by decide)
  have h8 : Entails.eval a c123 := h 122 (by decide)
  have h9 : Entails.eval a c141 := h 140 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c180 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨21, by decide⟩, false), (⟨12, by decide⟩, false), (⟨18, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f180 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c65, some c77, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p180 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked180 : lratChecker f180 p180 = .success := by decide +kernel
theorem unsat180 : Unsatisfiable (PosFin 31) f180 := by
  apply lratCheckerSound f180 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p180
  · intro a ha; simp [p180] at ha; subst a; trivial
  · exact checked180
theorem derived180 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c180 := by
  apply localUnsat_implies_entails f180 [c65, c77] c180 unsat180 (by rfl) a
  have h0 : Entails.eval a c65 := h 64 (by decide)
  have h1 : Entails.eval a c77 := h 76 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c181 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f181 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c175, some c159, some c177, some c179, some c160, some c108, some c180, some c139, some c49, some c11, some c140, some c26, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p181 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked181 : lratChecker f181 p181 = .success := by decide +kernel
theorem unsat181 : Unsatisfiable (PosFin 31) f181 := by
  apply lratCheckerSound f181 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p181
  · intro a ha; simp [p181] at ha; subst a; trivial
  · exact checked181
theorem derived181 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c181 := by
  apply localUnsat_implies_entails f181 [c175, c159, c177, c179, c160, c108, c180, c139, c49, c11, c140, c26] c181 unsat181 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c159 := h 158 (by decide)
  have h2 : Entails.eval a c177 := derived177 a h
  have h3 : Entails.eval a c179 := derived179 a h
  have h4 : Entails.eval a c160 := h 159 (by decide)
  have h5 : Entails.eval a c108 := h 107 (by decide)
  have h6 : Entails.eval a c180 := derived180 a h
  have h7 : Entails.eval a c139 := h 138 (by decide)
  have h8 : Entails.eval a c49 := h 48 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c140 := h 139 (by decide)
  have h11 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c182 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨12, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f182 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c181, some c175, some c49, some c11, some c47, some c26, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p182 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked182 : lratChecker f182 p182 = .success := by decide +kernel
theorem unsat182 : Unsatisfiable (PosFin 31) f182 := by
  apply lratCheckerSound f182 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p182
  · intro a ha; simp [p182] at ha; subst a; trivial
  · exact checked182
theorem derived182 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c182 := by
  apply localUnsat_implies_entails f182 [c181, c175, c49, c11, c47, c26] c182 unsat182 (by rfl) a
  have h0 : Entails.eval a c181 := derived181 a h
  have h1 : Entails.eval a c175 := derived175 a h
  have h2 : Entails.eval a c49 := h 48 (by decide)
  have h3 : Entails.eval a c11 := h 10 (by decide)
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c26 := h 25 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c183 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f183 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c181, some c175, some c159, some c182, some c44, some c50, some c151, some c77, some c3, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p183 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked183 : lratChecker f183 p183 = .success := by decide +kernel
theorem unsat183 : Unsatisfiable (PosFin 31) f183 := by
  apply lratCheckerSound f183 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p183
  · intro a ha; simp [p183] at ha; subst a; trivial
  · exact checked183
theorem derived183 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c183 := by
  apply localUnsat_implies_entails f183 [c181, c175, c159, c182, c44, c50, c151, c77, c3] c183 unsat183 (by rfl) a
  have h0 : Entails.eval a c181 := derived181 a h
  have h1 : Entails.eval a c175 := derived175 a h
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c182 := derived182 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c151 := h 150 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c3 := h 2 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c184 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f184 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c181, some c175, some c44, some c50, some c138, some c45, some c85, some c86, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p184 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked184 : lratChecker f184 p184 = .success := by decide +kernel
theorem unsat184 : Unsatisfiable (PosFin 31) f184 := by
  apply lratCheckerSound f184 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p184
  · intro a ha; simp [p184] at ha; subst a; trivial
  · exact checked184
theorem derived184 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c184 := by
  apply localUnsat_implies_entails f184 [c181, c175, c44, c50, c138, c45, c85, c86] c184 unsat184 (by rfl) a
  have h0 : Entails.eval a c181 := derived181 a h
  have h1 : Entails.eval a c175 := derived175 a h
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c50 := h 49 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c45 := h 44 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  have h7 : Entails.eval a c86 := h 85 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c185 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨11, by decide⟩, true), (⟨8, by decide⟩, false), (⟨12, by decide⟩, true), (⟨28, by decide⟩, true), (⟨29, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f185 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c162, some c128, some c26, some c80, some c92, some c63, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, true))]
def p185 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked185 : lratChecker f185 p185 = .success := by decide +kernel
theorem unsat185 : Unsatisfiable (PosFin 31) f185 := by
  apply lratCheckerSound f185 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p185
  · intro a ha; simp [p185] at ha; subst a; trivial
  · exact checked185
theorem derived185 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c185 := by
  apply localUnsat_implies_entails f185 [c162, c128, c26, c80, c92, c63] c185 unsat185 (by rfl) a
  have h0 : Entails.eval a c162 := h 161 (by decide)
  have h1 : Entails.eval a c128 := h 127 (by decide)
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c80 := h 79 (by decide)
  have h4 : Entails.eval a c92 := h 91 (by decide)
  have h5 : Entails.eval a c63 := h 62 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c186 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f186 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c175, some c181, some c183, some c184, some c47, some c185, some c16, some c131, some c31, some c93, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p186 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked186 : lratChecker f186 p186 = .success := by decide +kernel
theorem unsat186 : Unsatisfiable (PosFin 31) f186 := by
  apply lratCheckerSound f186 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p186
  · intro a ha; simp [p186] at ha; subst a; trivial
  · exact checked186
theorem derived186 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c186 := by
  apply localUnsat_implies_entails f186 [c175, c181, c183, c184, c47, c185, c16, c131, c31, c93] c186 unsat186 (by rfl) a
  have h0 : Entails.eval a c175 := derived175 a h
  have h1 : Entails.eval a c181 := derived181 a h
  have h2 : Entails.eval a c183 := derived183 a h
  have h3 : Entails.eval a c184 := derived184 a h
  have h4 : Entails.eval a c47 := h 46 (by decide)
  have h5 : Entails.eval a c185 := derived185 a h
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c131 := h 130 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  have h9 : Entails.eval a c93 := h 92 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c187 : DefaultClause 31 := directClause [(⟨8, by decide⟩, false), (⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f187 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c16, some c186, some c158, some c47, some c129, some c27, some c110, some c32, some (DefaultClause.unit (⟨8, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p187 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked187 : lratChecker f187 p187 = .success := by decide +kernel
theorem unsat187 : Unsatisfiable (PosFin 31) f187 := by
  apply lratCheckerSound f187 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p187
  · intro a ha; simp [p187] at ha; subst a; trivial
  · exact checked187
theorem derived187 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c187 := by
  apply localUnsat_implies_entails f187 [c16, c186, c158, c47, c129, c27, c110, c32] c187 unsat187 (by rfl) a
  have h0 : Entails.eval a c16 := h 15 (by decide)
  have h1 : Entails.eval a c186 := derived186 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c47 := h 46 (by decide)
  have h4 : Entails.eval a c129 := h 128 (by decide)
  have h5 : Entails.eval a c27 := h 26 (by decide)
  have h6 : Entails.eval a c110 := h 109 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c188 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f188 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c186, some c158, some c16, some c187, some c44, some c58, some c20, some c1, some c50, some c159, some c160, some c97, some c25, some c99, some c133, some c149, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p188 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked188 : lratChecker f188 p188 = .success := by decide +kernel
theorem unsat188 : Unsatisfiable (PosFin 31) f188 := by
  apply lratCheckerSound f188 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p188
  · intro a ha; simp [p188] at ha; subst a; trivial
  · exact checked188
theorem derived188 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c188 := by
  apply localUnsat_implies_entails f188 [c186, c158, c16, c187, c44, c58, c20, c1, c50, c159, c160, c97, c25, c99, c133, c149] c188 unsat188 (by rfl) a
  have h0 : Entails.eval a c186 := derived186 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c16 := h 15 (by decide)
  have h3 : Entails.eval a c187 := derived187 a h
  have h4 : Entails.eval a c44 := h 43 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c50 := h 49 (by decide)
  have h9 : Entails.eval a c159 := h 158 (by decide)
  have h10 : Entails.eval a c160 := h 159 (by decide)
  have h11 : Entails.eval a c97 := h 96 (by decide)
  have h12 : Entails.eval a c25 := h 24 (by decide)
  have h13 : Entails.eval a c99 := h 98 (by decide)
  have h14 : Entails.eval a c133 := h 132 (by decide)
  have h15 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c189 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true), (⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f189 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c188, some c162, some c44, some c20, some c1, some c160, some c156, some c148, some c130, some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p189 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked189 : lratChecker f189 p189 = .success := by decide +kernel
theorem unsat189 : Unsatisfiable (PosFin 31) f189 := by
  apply lratCheckerSound f189 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p189
  · intro a ha; simp [p189] at ha; subst a; trivial
  · exact checked189
theorem derived189 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c189 := by
  apply localUnsat_implies_entails f189 [c188, c162, c44, c20, c1, c160, c156, c148, c130] c189 unsat189 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c44 := h 43 (by decide)
  have h3 : Entails.eval a c20 := h 19 (by decide)
  have h4 : Entails.eval a c1 := h 0 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c156 := h 155 (by decide)
  have h7 : Entails.eval a c148 := h 147 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c190 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true), (⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f190 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c188, some c162, some c186, some c158, some c189, some c62, some c41, some c93, some c147, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p190 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked190 : lratChecker f190 p190 = .success := by decide +kernel
theorem unsat190 : Unsatisfiable (PosFin 31) f190 := by
  apply lratCheckerSound f190 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p190
  · intro a ha; simp [p190] at ha; subst a; trivial
  · exact checked190
theorem derived190 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c190 := by
  apply localUnsat_implies_entails f190 [c188, c162, c186, c158, c189, c62, c41, c93, c147] c190 unsat190 (by rfl) a
  have h0 : Entails.eval a c188 := derived188 a h
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c186 := derived186 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c189 := derived189 a h
  have h5 : Entails.eval a c62 := h 61 (by decide)
  have h6 : Entails.eval a c41 := h 40 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c191 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f191 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c186, some c158, some c188, some c162, some c190, some c68, some c111, some c13, some c4, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p191 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked191 : lratChecker f191 p191 = .success := by decide +kernel
theorem unsat191 : Unsatisfiable (PosFin 31) f191 := by
  apply lratCheckerSound f191 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p191
  · intro a ha; simp [p191] at ha; subst a; trivial
  · exact checked191
theorem derived191 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c191 := by
  apply localUnsat_implies_entails f191 [c186, c158, c188, c162, c190, c68, c111, c13, c4] c191 unsat191 (by rfl) a
  have h0 : Entails.eval a c186 := derived186 a h
  have h1 : Entails.eval a c158 := h 157 (by decide)
  have h2 : Entails.eval a c188 := derived188 a h
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c190 := derived190 a h
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c111 := h 110 (by decide)
  have h7 : Entails.eval a c13 := h 12 (by decide)
  have h8 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c192 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨14, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f192 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c191, some c186, some c158, some c60, some c107, some c13, some c76, some c64, some c139, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p192 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked192 : lratChecker f192 p192 = .success := by decide +kernel
theorem unsat192 : Unsatisfiable (PosFin 31) f192 := by
  apply lratCheckerSound f192 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p192
  · intro a ha; simp [p192] at ha; subst a; trivial
  · exact checked192
theorem derived192 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c192 := by
  apply localUnsat_implies_entails f192 [c191, c186, c158, c60, c107, c13, c76, c64, c139] c192 unsat192 (by rfl) a
  have h0 : Entails.eval a c191 := derived191 a h
  have h1 : Entails.eval a c186 := derived186 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c107 := h 106 (by decide)
  have h5 : Entails.eval a c13 := h 12 (by decide)
  have h6 : Entails.eval a c76 := h 75 (by decide)
  have h7 : Entails.eval a c64 := h 63 (by decide)
  have h8 : Entails.eval a c139 := h 138 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c193 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f193 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c192, some c162, some c191, some c186, some c158, some c86, some c33, some c27, some c152, some c53, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p193 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked193 : lratChecker f193 p193 = .success := by decide +kernel
theorem unsat193 : Unsatisfiable (PosFin 31) f193 := by
  apply lratCheckerSound f193 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p193
  · intro a ha; simp [p193] at ha; subst a; trivial
  · exact checked193
theorem derived193 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c193 := by
  apply localUnsat_implies_entails f193 [c192, c162, c191, c186, c158, c86, c33, c27, c152, c53] c193 unsat193 (by rfl) a
  have h0 : Entails.eval a c192 := derived192 a h
  have h1 : Entails.eval a c162 := h 161 (by decide)
  have h2 : Entails.eval a c191 := derived191 a h
  have h3 : Entails.eval a c186 := derived186 a h
  have h4 : Entails.eval a c158 := h 157 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c33 := h 32 (by decide)
  have h7 : Entails.eval a c27 := h 26 (by decide)
  have h8 : Entails.eval a c152 := h 151 (by decide)
  have h9 : Entails.eval a c53 := h 52 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c194 : DefaultClause 31 := directClause [(⟨14, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f194 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c191, some c193, some c42, some c94, some c5, some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p194 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked194 : lratChecker f194 p194 = .success := by decide +kernel
theorem unsat194 : Unsatisfiable (PosFin 31) f194 := by
  apply lratCheckerSound f194 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p194
  · intro a ha; simp [p194] at ha; subst a; trivial
  · exact checked194
theorem derived194 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c194 := by
  apply localUnsat_implies_entails f194 [c191, c193, c42, c94, c5] c194 unsat194 (by rfl) a
  have h0 : Entails.eval a c191 := derived191 a h
  have h1 : Entails.eval a c193 := derived193 a h
  have h2 : Entails.eval a c42 := h 41 (by decide)
  have h3 : Entails.eval a c94 := h 93 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c195 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f195 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c194, some c191, some c186, some c158, some c5, some c60, some c59, some c93, some c118, some c162, some c95, some c19, some c109, some c115, some c65, some c163, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p195 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked195 : lratChecker f195 p195 = .success := by decide +kernel
theorem unsat195 : Unsatisfiable (PosFin 31) f195 := by
  apply lratCheckerSound f195 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p195
  · intro a ha; simp [p195] at ha; subst a; trivial
  · exact checked195
theorem derived195 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c195 := by
  apply localUnsat_implies_entails f195 [c194, c191, c186, c158, c5, c60, c59, c93, c118, c162, c95, c19, c109, c115, c65, c163] c195 unsat195 (by rfl) a
  have h0 : Entails.eval a c194 := derived194 a h
  have h1 : Entails.eval a c191 := derived191 a h
  have h2 : Entails.eval a c186 := derived186 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c60 := h 59 (by decide)
  have h6 : Entails.eval a c59 := h 58 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c118 := h 117 (by decide)
  have h9 : Entails.eval a c162 := h 161 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c19 := h 18 (by decide)
  have h12 : Entails.eval a c109 := h 108 (by decide)
  have h13 : Entails.eval a c115 := h 114 (by decide)
  have h14 : Entails.eval a c65 := h 64 (by decide)
  have h15 : Entails.eval a c163 := h 162 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c196 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f196 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c194, some c186, some c158, some c195, some c41, some c74, some c43, some c58, some c20, some c72, some c84, some c110, some c159, some c143, some c119, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p196 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked196 : lratChecker f196 p196 = .success := by decide +kernel
theorem unsat196 : Unsatisfiable (PosFin 31) f196 := by
  apply lratCheckerSound f196 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p196
  · intro a ha; simp [p196] at ha; subst a; trivial
  · exact checked196
theorem derived196 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c196 := by
  apply localUnsat_implies_entails f196 [c194, c186, c158, c195, c41, c74, c43, c58, c20, c72, c84, c110, c159, c143, c119] c196 unsat196 (by rfl) a
  have h0 : Entails.eval a c194 := derived194 a h
  have h1 : Entails.eval a c186 := derived186 a h
  have h2 : Entails.eval a c158 := h 157 (by decide)
  have h3 : Entails.eval a c195 := derived195 a h
  have h4 : Entails.eval a c41 := h 40 (by decide)
  have h5 : Entails.eval a c74 := h 73 (by decide)
  have h6 : Entails.eval a c43 := h 42 (by decide)
  have h7 : Entails.eval a c58 := h 57 (by decide)
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c72 := h 71 (by decide)
  have h10 : Entails.eval a c84 := h 83 (by decide)
  have h11 : Entails.eval a c110 := h 109 (by decide)
  have h12 : Entails.eval a c159 := h 158 (by decide)
  have h13 : Entails.eval a c143 := h 142 (by decide)
  have h14 : Entails.eval a c119 := h 118 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c197 : DefaultClause 31 := directClause [(⟨16, by decide⟩, true), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f197 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c196, some c194, some c186, some c158, some c67, some c110, some c4, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p197 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked197 : lratChecker f197 p197 = .success := by decide +kernel
theorem unsat197 : Unsatisfiable (PosFin 31) f197 := by
  apply lratCheckerSound f197 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p197
  · intro a ha; simp [p197] at ha; subst a; trivial
  · exact checked197
theorem derived197 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c197 := by
  apply localUnsat_implies_entails f197 [c196, c194, c186, c158, c67, c110, c4] c197 unsat197 (by rfl) a
  have h0 : Entails.eval a c196 := derived196 a h
  have h1 : Entails.eval a c194 := derived194 a h
  have h2 : Entails.eval a c186 := derived186 a h
  have h3 : Entails.eval a c158 := h 157 (by decide)
  have h4 : Entails.eval a c67 := h 66 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c4 := h 3 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c198 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f198 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c197, some c194, some c41, some c43, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p198 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked198 : lratChecker f198 p198 = .success := by decide +kernel
theorem unsat198 : Unsatisfiable (PosFin 31) f198 := by
  apply lratCheckerSound f198 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p198
  · intro a ha; simp [p198] at ha; subst a; trivial
  · exact checked198
theorem derived198 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c198 := by
  apply localUnsat_implies_entails f198 [c197, c194, c41, c43] c198 unsat198 (by rfl) a
  have h0 : Entails.eval a c197 := derived197 a h
  have h1 : Entails.eval a c194 := derived194 a h
  have h2 : Entails.eval a c41 := h 40 (by decide)
  have h3 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c199 : DefaultClause 31 := directClause [(⟨30, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f199 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c191, some c194, some c197, some c198, some c5, some c93, some c95, some (DefaultClause.unit (⟨30, by decide⟩, true))]
def p199 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked199 : lratChecker f199 p199 = .success := by decide +kernel
theorem unsat199 : Unsatisfiable (PosFin 31) f199 := by
  apply lratCheckerSound f199 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p199
  · intro a ha; simp [p199] at ha; subst a; trivial
  · exact checked199
theorem derived199 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c199 := by
  apply localUnsat_implies_entails f199 [c191, c194, c197, c198, c5, c93, c95] c199 unsat199 (by rfl) a
  have h0 : Entails.eval a c191 := derived191 a h
  have h1 : Entails.eval a c194 := derived194 a h
  have h2 : Entails.eval a c197 := derived197 a h
  have h3 : Entails.eval a c198 := derived198 a h
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c200 : DefaultClause 31 := directClause [(⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f200 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c199, some c157, some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p200 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked200 : lratChecker f200 p200 = .success := by decide +kernel
theorem unsat200 : Unsatisfiable (PosFin 31) f200 := by
  apply lratCheckerSound f200 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p200
  · intro a ha; simp [p200] at ha; subst a; trivial
  · exact checked200
theorem derived200 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c200 := by
  apply localUnsat_implies_entails f200 [c199, c157] c200 unsat200 (by rfl) a
  have h0 : Entails.eval a c199 := derived199 a h
  have h1 : Entails.eval a c157 := h 156 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c201 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨15, by decide⟩, false), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f201 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c5, some c15, some c160, some c132, some c54, some c159, some c66, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p201 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked201 : lratChecker f201 p201 = .success := by decide +kernel
theorem unsat201 : Unsatisfiable (PosFin 31) f201 := by
  apply lratCheckerSound f201 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p201
  · intro a ha; simp [p201] at ha; subst a; trivial
  · exact checked201
theorem derived201 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c201 := by
  apply localUnsat_implies_entails f201 [c200, c5, c15, c160, c132, c54, c159, c66] c201 unsat201 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c15 := h 14 (by decide)
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c132 := h 131 (by decide)
  have h5 : Entails.eval a c54 := h 53 (by decide)
  have h6 : Entails.eval a c159 := h 158 (by decide)
  have h7 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c202 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨9, by decide⟩, true), (⟨15, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f202 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c201, some c114, some c153, some c154, some c75, some c56, some c98, some c161, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p202 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked202 : lratChecker f202 p202 = .success := by decide +kernel
theorem unsat202 : Unsatisfiable (PosFin 31) f202 := by
  apply lratCheckerSound f202 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p202
  · intro a ha; simp [p202] at ha; subst a; trivial
  · exact checked202
theorem derived202 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c202 := by
  apply localUnsat_implies_entails f202 [c200, c201, c114, c153, c154, c75, c56, c98, c161] c202 unsat202 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c201 := derived201 a h
  have h2 : Entails.eval a c114 := h 113 (by decide)
  have h3 : Entails.eval a c153 := h 152 (by decide)
  have h4 : Entails.eval a c154 := h 153 (by decide)
  have h5 : Entails.eval a c75 := h 74 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c98 := h 97 (by decide)
  have h8 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c203 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨6, by decide⟩, false), (⟨15, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f203 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c103, some c117, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p203 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked203 : lratChecker f203 p203 = .success := by decide +kernel
theorem unsat203 : Unsatisfiable (PosFin 31) f203 := by
  apply lratCheckerSound f203 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p203
  · intro a ha; simp [p203] at ha; subst a; trivial
  · exact checked203
theorem derived203 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c203 := by
  apply localUnsat_implies_entails f203 [c200, c103, c117] c203 unsat203 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c103 := h 102 (by decide)
  have h2 : Entails.eval a c117 := h 116 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c204 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨12, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f204 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c201, some c203, some c160, some c54, some c202, some c155, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p204 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked204 : lratChecker f204 p204 = .success := by decide +kernel
theorem unsat204 : Unsatisfiable (PosFin 31) f204 := by
  apply lratCheckerSound f204 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p204
  · intro a ha; simp [p204] at ha; subst a; trivial
  · exact checked204
theorem derived204 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c204 := by
  apply localUnsat_implies_entails f204 [c200, c201, c203, c160, c54, c202, c155] c204 unsat204 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c201 := derived201 a h
  have h2 : Entails.eval a c203 := derived203 a h
  have h3 : Entails.eval a c160 := h 159 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  have h5 : Entails.eval a c202 := derived202 a h
  have h6 : Entails.eval a c155 := h 154 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c205 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨6, by decide⟩, true), (⟨15, by decide⟩, true), (⟨12, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f205 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c199, some c200, some c5, some c132, some c24, some c83, some c144, some c120, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false))]
def p205 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked205 : lratChecker f205 p205 = .success := by decide +kernel
theorem unsat205 : Unsatisfiable (PosFin 31) f205 := by
  apply lratCheckerSound f205 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p205
  · intro a ha; simp [p205] at ha; subst a; trivial
  · exact checked205
theorem derived205 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c205 := by
  apply localUnsat_implies_entails f205 [c199, c200, c5, c132, c24, c83, c144, c120] c205 unsat205 (by rfl) a
  have h0 : Entails.eval a c199 := derived199 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c132 := h 131 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  have h7 : Entails.eval a c120 := h 119 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c206 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f206 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c204, some c112, some c5, some c205, some c160, some c130, some c57, some c103, some c145, some c116, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p206 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked206 : lratChecker f206 p206 = .success := by decide +kernel
theorem unsat206 : Unsatisfiable (PosFin 31) f206 := by
  apply lratCheckerSound f206 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p206
  · intro a ha; simp [p206] at ha; subst a; trivial
  · exact checked206
theorem derived206 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c206 := by
  apply localUnsat_implies_entails f206 [c200, c204, c112, c5, c205, c160, c130, c57, c103, c145, c116] c206 unsat206 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c204 := derived204 a h
  have h2 : Entails.eval a c112 := h 111 (by decide)
  have h3 : Entails.eval a c5 := h 4 (by decide)
  have h4 : Entails.eval a c205 := derived205 a h
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c130 := h 129 (by decide)
  have h7 : Entails.eval a c57 := h 56 (by decide)
  have h8 : Entails.eval a c103 := h 102 (by decide)
  have h9 : Entails.eval a c145 := h 144 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c207 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f207 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c206, some c69, some c57, some c73, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p207 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked207 : lratChecker f207 p207 = .success := by decide +kernel
theorem unsat207 : Unsatisfiable (PosFin 31) f207 := by
  apply lratCheckerSound f207 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p207
  · intro a ha; simp [p207] at ha; subst a; trivial
  · exact checked207
theorem derived207 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c207 := by
  apply localUnsat_implies_entails f207 [c200, c206, c69, c57, c73] c207 unsat207 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c206 := derived206 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c57 := h 56 (by decide)
  have h4 : Entails.eval a c73 := h 72 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c208 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f208 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c199, some c69, some c71, some c207, some c160, some c48, some c22, some c1, some c39, some c92, some c21, some c98, some c146, some c128, some c106, some c90, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p208 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked208 : lratChecker f208 p208 = .success := by decide +kernel
theorem unsat208 : Unsatisfiable (PosFin 31) f208 := by
  apply lratCheckerSound f208 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p208
  · intro a ha; simp [p208] at ha; subst a; trivial
  · exact checked208
theorem derived208 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c208 := by
  apply localUnsat_implies_entails f208 [c200, c199, c69, c71, c207, c160, c48, c22, c1, c39, c92, c21, c98, c146, c128, c106, c90] c208 unsat208 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c199 := derived199 a h
  have h2 : Entails.eval a c69 := h 68 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c207 := derived207 a h
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c48 := h 47 (by decide)
  have h7 : Entails.eval a c22 := h 21 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c39 := h 38 (by decide)
  have h10 : Entails.eval a c92 := h 91 (by decide)
  have h11 : Entails.eval a c21 := h 20 (by decide)
  have h12 : Entails.eval a c98 := h 97 (by decide)
  have h13 : Entails.eval a c146 := h 145 (by decide)
  have h14 : Entails.eval a c128 := h 127 (by decide)
  have h15 : Entails.eval a c106 := h 105 (by decide)
  have h16 : Entails.eval a c90 := h 89 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c209 : DefaultClause 31 := directClause [(⟨14, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f209 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c206, some c208, some (DefaultClause.unit (⟨14, by decide⟩, false))]
def p209 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked209 : lratChecker f209 p209 = .success := by decide +kernel
theorem unsat209 : Unsatisfiable (PosFin 31) f209 := by
  apply lratCheckerSound f209 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p209
  · intro a ha; simp [p209] at ha; subst a; trivial
  · exact checked209
theorem derived209 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c209 := by
  apply localUnsat_implies_entails f209 [c206, c208] c209 unsat209 (by rfl) a
  have h0 : Entails.eval a c206 := derived206 a h
  have h1 : Entails.eval a c208 := derived208 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c210 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true), (⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f210 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c209, some c101, some c100, some c105, some c102, some c162, some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p210 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked210 : lratChecker f210 p210 = .success := by decide +kernel
theorem unsat210 : Unsatisfiable (PosFin 31) f210 := by
  apply lratCheckerSound f210 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p210
  · intro a ha; simp [p210] at ha; subst a; trivial
  · exact checked210
theorem derived210 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c210 := by
  apply localUnsat_implies_entails f210 [c200, c209, c101, c100, c105, c102, c162] c210 unsat210 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c101 := h 100 (by decide)
  have h3 : Entails.eval a c100 := h 99 (by decide)
  have h4 : Entails.eval a c105 := h 104 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c211 : DefaultClause 31 := directClause [(⟨27, by decide⟩, false), (⟨15, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f211 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c209, some c71, some c70, some c48, some c210, some c153, some c34, some c36, some (DefaultClause.unit (⟨27, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p211 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked211 : lratChecker f211 p211 = .success := by decide +kernel
theorem unsat211 : Unsatisfiable (PosFin 31) f211 := by
  apply lratCheckerSound f211 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p211
  · intro a ha; simp [p211] at ha; subst a; trivial
  · exact checked211
theorem derived211 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c211 := by
  apply localUnsat_implies_entails f211 [c200, c209, c71, c70, c48, c210, c153, c34, c36] c211 unsat211 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c71 := h 70 (by decide)
  have h3 : Entails.eval a c70 := h 69 (by decide)
  have h4 : Entails.eval a c48 := h 47 (by decide)
  have h5 : Entails.eval a c210 := derived210 a h
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c34 := h 33 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c212 : DefaultClause 31 := directClause [(⟨15, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f212 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c200, some c70, some c71, some c211, some c160, some c9, some c73, some c15, some c104, some c153, some c6, some c122, some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p212 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked212 : lratChecker f212 p212 = .success := by decide +kernel
theorem unsat212 : Unsatisfiable (PosFin 31) f212 := by
  apply lratCheckerSound f212 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p212
  · intro a ha; simp [p212] at ha; subst a; trivial
  · exact checked212
theorem derived212 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c212 := by
  apply localUnsat_implies_entails f212 [c209, c200, c70, c71, c211, c160, c9, c73, c15, c104, c153, c6, c122] c212 unsat212 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c71 := h 70 (by decide)
  have h4 : Entails.eval a c211 := derived211 a h
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c73 := h 72 (by decide)
  have h8 : Entails.eval a c15 := h 14 (by decide)
  have h9 : Entails.eval a c104 := h 103 (by decide)
  have h10 : Entails.eval a c153 := h 152 (by decide)
  have h11 : Entails.eval a c6 := h 5 (by decide)
  have h12 : Entails.eval a c122 := h 121 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c213 : DefaultClause 31 := directClause [(⟨27, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f213 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c200, some c199, some c212, some c70, some c160, some c9, some c24, some c23, some c37, some c91, some c127, some (DefaultClause.unit (⟨27, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p213 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked213 : lratChecker f213 p213 = .success := by decide +kernel
theorem unsat213 : Unsatisfiable (PosFin 31) f213 := by
  apply lratCheckerSound f213 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p213
  · intro a ha; simp [p213] at ha; subst a; trivial
  · exact checked213
theorem derived213 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c213 := by
  apply localUnsat_implies_entails f213 [c209, c200, c199, c212, c70, c160, c9, c24, c23, c37, c91, c127] c213 unsat213 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c199 := derived199 a h
  have h3 : Entails.eval a c212 := derived212 a h
  have h4 : Entails.eval a c70 := h 69 (by decide)
  have h5 : Entails.eval a c160 := h 159 (by decide)
  have h6 : Entails.eval a c9 := h 8 (by decide)
  have h7 : Entails.eval a c24 := h 23 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c37 := h 36 (by decide)
  have h10 : Entails.eval a c91 := h 90 (by decide)
  have h11 : Entails.eval a c127 := h 126 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c214 : DefaultClause 31 := directClause [(⟨9, by decide⟩, true), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f214 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c209, some c199, some c213, some c212, some c70, some c24, some c2, some c23, some c87, some c37, some c135, some c158, some c152, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p214 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked214 : lratChecker f214 p214 = .success := by decide +kernel
theorem unsat214 : Unsatisfiable (PosFin 31) f214 := by
  apply lratCheckerSound f214 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p214
  · intro a ha; simp [p214] at ha; subst a; trivial
  · exact checked214
theorem derived214 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c214 := by
  apply localUnsat_implies_entails f214 [c200, c209, c199, c213, c212, c70, c24, c2, c23, c87, c37, c135, c158, c152] c214 unsat214 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c199 := derived199 a h
  have h3 : Entails.eval a c213 := derived213 a h
  have h4 : Entails.eval a c212 := derived212 a h
  have h5 : Entails.eval a c70 := h 69 (by decide)
  have h6 : Entails.eval a c24 := h 23 (by decide)
  have h7 : Entails.eval a c2 := h 1 (by decide)
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c87 := h 86 (by decide)
  have h10 : Entails.eval a c37 := h 36 (by decide)
  have h11 : Entails.eval a c135 := h 134 (by decide)
  have h12 : Entails.eval a c158 := h 157 (by decide)
  have h13 : Entails.eval a c152 := h 151 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c215 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f215 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c76, some c51, some c162, some (DefaultClause.unit (⟨9, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p215 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked215 : lratChecker f215 p215 = .success := by decide +kernel
theorem unsat215 : Unsatisfiable (PosFin 31) f215 := by
  apply lratCheckerSound f215 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p215
  · intro a ha; simp [p215] at ha; subst a; trivial
  · exact checked215
theorem derived215 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c215 := by
  apply localUnsat_implies_entails f215 [c209, c76, c51, c162] c215 unsat215 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c76 := h 75 (by decide)
  have h2 : Entails.eval a c51 := h 50 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c216 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f216 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c214, some c215, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p216 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked216 : lratChecker f216 p216 = .success := by decide +kernel
theorem unsat216 : Unsatisfiable (PosFin 31) f216 := by
  apply lratCheckerSound f216 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p216
  · intro a ha; simp [p216] at ha; subst a; trivial
  · exact checked216
theorem derived216 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c216 := by
  apply localUnsat_implies_entails f216 [c214, c215] c216 unsat216 (by rfl) a
  have h0 : Entails.eval a c214 := derived214 a h
  have h1 : Entails.eval a c215 := derived215 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c217 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f217 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c216, some c209, some c200, some c162, some c18, some c14, some c80, some c5, some c28, some c36, some c78, some c113, some c154, some c121, some c114, some c46, some c164, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p217 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked217 : lratChecker f217 p217 = .success := by decide +kernel
theorem unsat217 : Unsatisfiable (PosFin 31) f217 := by
  apply lratCheckerSound f217 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p217
  · intro a ha; simp [p217] at ha; subst a; trivial
  · exact checked217
theorem derived217 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c217 := by
  apply localUnsat_implies_entails f217 [c216, c209, c200, c162, c18, c14, c80, c5, c28, c36, c78, c113, c154, c121, c114, c46, c164] c217 unsat217 (by rfl) a
  have h0 : Entails.eval a c216 := derived216 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c200 := derived200 a h
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  have h5 : Entails.eval a c14 := h 13 (by decide)
  have h6 : Entails.eval a c80 := h 79 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c28 := h 27 (by decide)
  have h9 : Entails.eval a c36 := h 35 (by decide)
  have h10 : Entails.eval a c78 := h 77 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c154 := h 153 (by decide)
  have h13 : Entails.eval a c121 := h 120 (by decide)
  have h14 : Entails.eval a c114 := h 113 (by decide)
  have h15 : Entails.eval a c46 := h 45 (by decide)
  have h16 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c218 : DefaultClause 31 := directClause [(⟨20, by decide⟩, false), (⟨26, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f218 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c209, some c216, some c14, some c60, some c29, some c158, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, true))]
def p218 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked218 : lratChecker f218 p218 = .success := by decide +kernel
theorem unsat218 : Unsatisfiable (PosFin 31) f218 := by
  apply lratCheckerSound f218 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p218
  · intro a ha; simp [p218] at ha; subst a; trivial
  · exact checked218
theorem derived218 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c218 := by
  apply localUnsat_implies_entails f218 [c200, c209, c216, c14, c60, c29, c158] c218 unsat218 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c216 := derived216 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c60 := h 59 (by decide)
  have h5 : Entails.eval a c29 := h 28 (by decide)
  have h6 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c219 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f219 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c216, some c200, some c199, some c217, some c218, some c55, some c5, some c59, some c29, some c154, some c156, some c125, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p219 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked219 : lratChecker f219 p219 = .success := by decide +kernel
theorem unsat219 : Unsatisfiable (PosFin 31) f219 := by
  apply lratCheckerSound f219 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p219
  · intro a ha; simp [p219] at ha; subst a; trivial
  · exact checked219
theorem derived219 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c219 := by
  apply localUnsat_implies_entails f219 [c209, c216, c200, c199, c217, c218, c55, c5, c59, c29, c154, c156, c125] c219 unsat219 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c216 := derived216 a h
  have h2 : Entails.eval a c200 := derived200 a h
  have h3 : Entails.eval a c199 := derived199 a h
  have h4 : Entails.eval a c217 := derived217 a h
  have h5 : Entails.eval a c218 := derived218 a h
  have h6 : Entails.eval a c55 := h 54 (by decide)
  have h7 : Entails.eval a c5 := h 4 (by decide)
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c29 := h 28 (by decide)
  have h10 : Entails.eval a c154 := h 153 (by decide)
  have h11 : Entails.eval a c156 := h 155 (by decide)
  have h12 : Entails.eval a c125 := h 124 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c220 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨11, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f220 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c68, some c40, some c158, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, true))]
def p220 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked220 : lratChecker f220 p220 = .success := by decide +kernel
theorem unsat220 : Unsatisfiable (PosFin 31) f220 := by
  apply lratCheckerSound f220 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p220
  · intro a ha; simp [p220] at ha; subst a; trivial
  · exact checked220
theorem derived220 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c220 := by
  apply localUnsat_implies_entails f220 [c209, c68, c40, c158] c220 unsat220 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c68 := h 67 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c221 : DefaultClause 31 := directClause [(⟨9, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f221 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c209, some c216, some c217, some c55, some c219, some c220, some (DefaultClause.unit (⟨9, by decide⟩, true))]
def p221 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked221 : lratChecker f221 p221 = .success := by decide +kernel
theorem unsat221 : Unsatisfiable (PosFin 31) f221 := by
  apply lratCheckerSound f221 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p221
  · intro a ha; simp [p221] at ha; subst a; trivial
  · exact checked221
theorem derived221 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c221 := by
  apply localUnsat_implies_entails f221 [c209, c216, c217, c55, c219, c220] c221 unsat221 (by rfl) a
  have h0 : Entails.eval a c209 := derived209 a h
  have h1 : Entails.eval a c216 := derived216 a h
  have h2 : Entails.eval a c217 := derived217 a h
  have h3 : Entails.eval a c55 := h 54 (by decide)
  have h4 : Entails.eval a c219 := derived219 a h
  have h5 : Entails.eval a c220 := derived220 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c222 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f222 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c200, some c209, some c216, some c14, some c220, some c162, some c55, some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p222 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked222 : lratChecker f222 p222 = .success := by decide +kernel
theorem unsat222 : Unsatisfiable (PosFin 31) f222 := by
  apply lratCheckerSound f222 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p222
  · intro a ha; simp [p222] at ha; subst a; trivial
  · exact checked222
theorem derived222 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c222 := by
  apply localUnsat_implies_entails f222 [c200, c209, c216, c14, c220, c162, c55] c222 unsat222 (by rfl) a
  have h0 : Entails.eval a c200 := derived200 a h
  have h1 : Entails.eval a c209 := derived209 a h
  have h2 : Entails.eval a c216 := derived216 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  have h4 : Entails.eval a c220 := derived220 a h
  have h5 : Entails.eval a c162 := h 161 (by decide)
  have h6 : Entails.eval a c55 := h 54 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c223 : DefaultClause 31 := directClause [(⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f223 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c222, some c216, some c5, some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p223 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked223 : lratChecker f223 p223 = .success := by decide +kernel
theorem unsat223 : Unsatisfiable (PosFin 31) f223 := by
  apply lratCheckerSound f223 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p223
  · intro a ha; simp [p223] at ha; subst a; trivial
  · exact checked223
theorem derived223 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c223 := by
  apply localUnsat_implies_entails f223 [c222, c216, c5] c223 unsat223 (by rfl) a
  have h0 : Entails.eval a c222 := derived222 a h
  have h1 : Entails.eval a c216 := derived216 a h
  have h2 : Entails.eval a c5 := h 4 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c224 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f224 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c223, some c200, some c209, some c113, some (DefaultClause.unit (⟨17, by decide⟩, true))]
def p224 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked224 : lratChecker f224 p224 = .success := by decide +kernel
theorem unsat224 : Unsatisfiable (PosFin 31) f224 := by
  apply lratCheckerSound f224 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p224
  · intro a ha; simp [p224] at ha; subst a; trivial
  · exact checked224
theorem derived224 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c224 := by
  apply localUnsat_implies_entails f224 [c223, c200, c209, c113] c224 unsat224 (by rfl) a
  have h0 : Entails.eval a c223 := derived223 a h
  have h1 : Entails.eval a c200 := derived200 a h
  have h2 : Entails.eval a c209 := derived209 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c225 : DefaultClause 31 := directClause [(⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f225 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c223, some c221, some c200, some c153, some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p225 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked225 : lratChecker f225 p225 = .success := by decide +kernel
theorem unsat225 : Unsatisfiable (PosFin 31) f225 := by
  apply lratCheckerSound f225 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p225
  · intro a ha; simp [p225] at ha; subst a; trivial
  · exact checked225
theorem derived225 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c225 := by
  apply localUnsat_implies_entails f225 [c223, c221, c200, c153] c225 unsat225 (by rfl) a
  have h0 : Entails.eval a c223 := derived223 a h
  have h1 : Entails.eval a c221 := derived221 a h
  have h2 : Entails.eval a c200 := derived200 a h
  have h3 : Entails.eval a c153 := h 152 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c226 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f226 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c224, some c216, some c222, some c8, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p226 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked226 : lratChecker f226 p226 = .success := by decide +kernel
theorem unsat226 : Unsatisfiable (PosFin 31) f226 := by
  apply lratCheckerSound f226 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p226
  · intro a ha; simp [p226] at ha; subst a; trivial
  · exact checked226
theorem derived226 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c226 := by
  apply localUnsat_implies_entails f226 [c224, c216, c222, c8] c226 unsat226 (by rfl) a
  have h0 : Entails.eval a c224 := derived224 a h
  have h1 : Entails.eval a c216 := derived216 a h
  have h2 : Entails.eval a c222 := derived222 a h
  have h3 : Entails.eval a c8 := h 7 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c227 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f227 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c225, some c226, some c223, some c200, some c154]
def p227 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked227 : lratChecker f227 p227 = .success := by decide +kernel
theorem unsat227 : Unsatisfiable (PosFin 31) f227 := by
  apply lratCheckerSound f227 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p227
  · intro a ha; simp [p227] at ha; subst a; trivial
  · exact checked227
theorem derived227 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c227 := by
  apply localUnsat_implies_entails f227 [c225, c226, c223, c200, c154] c227 unsat227 (by rfl) a
  have h0 : Entails.eval a c225 := derived225 a h
  have h1 : Entails.eval a c226 := derived226 a h
  have h2 : Entails.eval a c223 := derived223 a h
  have h3 : Entails.eval a c200 := derived200 a h
  have h4 : Entails.eval a c154 := h 153 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived227

end CochromaticTwenty.Certificates.Z12Direct_5_5_6
