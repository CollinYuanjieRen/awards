import MerLeanExperiment.Certificates.Z12Direct_5_8_2.Steps0000_0099

/-! Generated from the actual pinned z12direct_5_8_2-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.Z12Direct_5_8_2
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c396 : DefaultClause 31 := directClause [(⟨21, by decide⟩, false), (⟨23, by decide⟩, false), (⟨26, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f396 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c104, some c19, some c125, some c124, some c22, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p396 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked396 : lratChecker f396 p396 = .success := by decide +kernel
theorem unsat396 : Unsatisfiable (PosFin 31) f396 := by
  apply lratCheckerSound f396 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p396
  · intro a ha; simp [p396] at ha; subst a; trivial
  · exact checked396
theorem derived396 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c396 := by
  apply localUnsat_implies_entails f396 [c104, c19, c125, c124, c22] c396 unsat396 (by rfl) a
  have h0 : Entails.eval a c104 := h 103 (by decide)
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c125 := h 124 (by decide)
  have h3 : Entails.eval a c124 := h 123 (by decide)
  have h4 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c397 : DefaultClause 31 := directClause [(⟨26, by decide⟩, true), (⟨28, by decide⟩, true), (⟨3, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f397 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c394, some c317, some c319, some c396, some c187, some c56, some c21, some c153, some c206, some (DefaultClause.unit (⟨26, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p397 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked397 : lratChecker f397 p397 = .success := by decide +kernel
theorem unsat397 : Unsatisfiable (PosFin 31) f397 := by
  apply lratCheckerSound f397 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p397
  · intro a ha; simp [p397] at ha; subst a; trivial
  · exact checked397
theorem derived397 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c397 := by
  apply localUnsat_implies_entails f397 [c370, c394, c317, c319, c396, c187, c56, c21, c153, c206] c397 unsat397 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c317 := derived317 a h
  have h3 : Entails.eval a c319 := derived319 a h
  have h4 : Entails.eval a c396 := derived396 a h
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  have h7 : Entails.eval a c21 := h 20 (by decide)
  have h8 : Entails.eval a c153 := h 152 (by decide)
  have h9 : Entails.eval a c206 := h 205 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c398 : DefaultClause 31 := directClause [(⟨26, by decide⟩, false), (⟨3, by decide⟩, true), (⟨20, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f398 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c99, some c100, some c150, some c54, some (DefaultClause.unit (⟨26, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p398 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked398 : lratChecker f398 p398 = .success := by decide +kernel
theorem unsat398 : Unsatisfiable (PosFin 31) f398 := by
  apply lratCheckerSound f398 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p398
  · intro a ha; simp [p398] at ha; subst a; trivial
  · exact checked398
theorem derived398 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c398 := by
  apply localUnsat_implies_entails f398 [c370, c99, c100, c150, c54] c398 unsat398 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c100 := h 99 (by decide)
  have h3 : Entails.eval a c150 := h 149 (by decide)
  have h4 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c399 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true), (⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f399 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c395, some c394, some c398, some c397, some c101, some c102, some c150, some c54, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p399 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked399 : lratChecker f399 p399 = .success := by decide +kernel
theorem unsat399 : Unsatisfiable (PosFin 31) f399 := by
  apply lratCheckerSound f399 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p399
  · intro a ha; simp [p399] at ha; subst a; trivial
  · exact checked399
theorem derived399 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c399 := by
  apply localUnsat_implies_entails f399 [c370, c395, c394, c398, c397, c101, c102, c150, c54] c399 unsat399 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c395 := derived395 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c398 := derived398 a h
  have h4 : Entails.eval a c397 := derived397 a h
  have h5 : Entails.eval a c101 := h 100 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c150 := h 149 (by decide)
  have h8 : Entails.eval a c54 := h 53 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c400 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨24, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f400 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c395, some c399, some c391, some c197, some c185, some c22, some c102, some c100, some c318, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p400 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked400 : lratChecker f400 p400 = .success := by decide +kernel
theorem unsat400 : Unsatisfiable (PosFin 31) f400 := by
  apply lratCheckerSound f400 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p400
  · intro a ha; simp [p400] at ha; subst a; trivial
  · exact checked400
theorem derived400 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c400 := by
  apply localUnsat_implies_entails f400 [c395, c399, c391, c197, c185, c22, c102, c100, c318] c400 unsat400 (by rfl) a
  have h0 : Entails.eval a c395 := derived395 a h
  have h1 : Entails.eval a c399 := derived399 a h
  have h2 : Entails.eval a c391 := derived391 a h
  have h3 : Entails.eval a c197 := h 196 (by decide)
  have h4 : Entails.eval a c185 := h 184 (by decide)
  have h5 : Entails.eval a c22 := h 21 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  have h7 : Entails.eval a c100 := h 99 (by decide)
  have h8 : Entails.eval a c318 := derived318 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c401 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f401 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c24, some c394, some c134, some c147, some c50, some c191, some c7, some c224, some c161, some (DefaultClause.unit (⟨28, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p401 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked401 : lratChecker f401 p401 = .success := by decide +kernel
theorem unsat401 : Unsatisfiable (PosFin 31) f401 := by
  apply lratCheckerSound f401 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p401
  · intro a ha; simp [p401] at ha; subst a; trivial
  · exact checked401
theorem derived401 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c401 := by
  apply localUnsat_implies_entails f401 [c370, c24, c394, c134, c147, c50, c191, c7, c224, c161] c401 unsat401 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c134 := h 133 (by decide)
  have h4 : Entails.eval a c147 := h 146 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c7 := h 6 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  have h9 : Entails.eval a c161 := h 160 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c402 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨10, by decide⟩, false), (⟨28, by decide⟩, true), (⟨24, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f402 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c206, some c177, some c56, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p402 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked402 : lratChecker f402 p402 = .success := by decide +kernel
theorem unsat402 : Unsatisfiable (PosFin 31) f402 := by
  apply lratCheckerSound f402 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p402
  · intro a ha; simp [p402] at ha; subst a; trivial
  · exact checked402
theorem derived402 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c402 := by
  apply localUnsat_implies_entails f402 [c370, c206, c177, c56] c402 unsat402 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c206 := h 205 (by decide)
  have h2 : Entails.eval a c177 := h 176 (by decide)
  have h3 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c403 : DefaultClause 31 := directClause [(⟨24, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f403 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c394, some c400, some c401, some c23, some c402, some c191, some c153, some c115, some c56, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p403 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked403 : lratChecker f403 p403 = .success := by decide +kernel
theorem unsat403 : Unsatisfiable (PosFin 31) f403 := by
  apply lratCheckerSound f403 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p403
  · intro a ha; simp [p403] at ha; subst a; trivial
  · exact checked403
theorem derived403 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c403 := by
  apply localUnsat_implies_entails f403 [c370, c394, c400, c401, c23, c402, c191, c153, c115, c56] c403 unsat403 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c400 := derived400 a h
  have h3 : Entails.eval a c401 := derived401 a h
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c402 := derived402 a h
  have h6 : Entails.eval a c191 := h 190 (by decide)
  have h7 : Entails.eval a c153 := h 152 (by decide)
  have h8 : Entails.eval a c115 := h 114 (by decide)
  have h9 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c404 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨12, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f404 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c401, some c394, some c191, some c153, some c115, some c56, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p404 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked404 : lratChecker f404 p404 = .success := by decide +kernel
theorem unsat404 : Unsatisfiable (PosFin 31) f404 := by
  apply lratCheckerSound f404 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p404
  · intro a ha; simp [p404] at ha; subst a; trivial
  · exact checked404
theorem derived404 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c404 := by
  apply localUnsat_implies_entails f404 [c370, c401, c394, c191, c153, c115, c56] c404 unsat404 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c401 := derived401 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c191 := h 190 (by decide)
  have h4 : Entails.eval a c153 := h 152 (by decide)
  have h5 : Entails.eval a c115 := h 114 (by decide)
  have h6 : Entails.eval a c56 := h 55 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c405 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f405 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c403, some c394, some c24, some c401, some c23, some c404, some c217, some c178, some c114, some c116, some c79, some c27, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p405 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked405 : lratChecker f405 p405 = .success := by decide +kernel
theorem unsat405 : Unsatisfiable (PosFin 31) f405 := by
  apply lratCheckerSound f405 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p405
  · intro a ha; simp [p405] at ha; subst a; trivial
  · exact checked405
theorem derived405 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c405 := by
  apply localUnsat_implies_entails f405 [c370, c403, c394, c24, c401, c23, c404, c217, c178, c114, c116, c79, c27] c405 unsat405 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c403 := derived403 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c24 := h 23 (by decide)
  have h4 : Entails.eval a c401 := derived401 a h
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c404 := derived404 a h
  have h7 : Entails.eval a c217 := h 216 (by decide)
  have h8 : Entails.eval a c178 := h 177 (by decide)
  have h9 : Entails.eval a c114 := h 113 (by decide)
  have h10 : Entails.eval a c116 := h 115 (by decide)
  have h11 : Entails.eval a c79 := h 78 (by decide)
  have h12 : Entails.eval a c27 := h 26 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c406 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f406 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c405, some c403, some c394, some c113, some c72, some c62, some c224, some c125, some c79, some c269, some c108, some c176, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p406 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked406 : lratChecker f406 p406 = .success := by decide +kernel
theorem unsat406 : Unsatisfiable (PosFin 31) f406 := by
  apply lratCheckerSound f406 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p406
  · intro a ha; simp [p406] at ha; subst a; trivial
  · exact checked406
theorem derived406 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c406 := by
  apply localUnsat_implies_entails f406 [c370, c405, c403, c394, c113, c72, c62, c224, c125, c79, c269, c108, c176] c406 unsat406 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c405 := derived405 a h
  have h2 : Entails.eval a c403 := derived403 a h
  have h3 : Entails.eval a c394 := derived394 a h
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c72 := h 71 (by decide)
  have h6 : Entails.eval a c62 := h 61 (by decide)
  have h7 : Entails.eval a c224 := h 223 (by decide)
  have h8 : Entails.eval a c125 := h 124 (by decide)
  have h9 : Entails.eval a c79 := h 78 (by decide)
  have h10 : Entails.eval a c269 := h 268 (by decide)
  have h11 : Entails.eval a c108 := h 107 (by decide)
  have h12 : Entails.eval a c176 := h 175 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c407 : DefaultClause 31 := directClause [(⟨10, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨24, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f407 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c95, some c178, some c117, some c93, some c103, some (DefaultClause.unit (⟨10, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false))]
def p407 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked407 : lratChecker f407 p407 = .success := by decide +kernel
theorem unsat407 : Unsatisfiable (PosFin 31) f407 := by
  apply lratCheckerSound f407 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p407
  · intro a ha; simp [p407] at ha; subst a; trivial
  · exact checked407
theorem derived407 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c407 := by
  apply localUnsat_implies_entails f407 [c370, c95, c178, c117, c93, c103] c407 unsat407 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c178 := h 177 (by decide)
  have h3 : Entails.eval a c117 := h 116 (by decide)
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c408 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false), (⟨28, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f408 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c405, some c403, some c406, some c407, some c110, some c108, some c183, some c2, some c13, some c224, some c237, some c11, some c372, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p408 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked408 : lratChecker f408 p408 = .success := by decide +kernel
theorem unsat408 : Unsatisfiable (PosFin 31) f408 := by
  apply lratCheckerSound f408 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p408
  · intro a ha; simp [p408] at ha; subst a; trivial
  · exact checked408
theorem derived408 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c408 := by
  apply localUnsat_implies_entails f408 [c370, c405, c403, c406, c407, c110, c108, c183, c2, c13, c224, c237, c11, c372] c408 unsat408 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c405 := derived405 a h
  have h2 : Entails.eval a c403 := derived403 a h
  have h3 : Entails.eval a c406 := derived406 a h
  have h4 : Entails.eval a c407 := derived407 a h
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c183 := h 182 (by decide)
  have h8 : Entails.eval a c2 := h 1 (by decide)
  have h9 : Entails.eval a c13 := h 12 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c237 := h 236 (by decide)
  have h12 : Entails.eval a c11 := h 10 (by decide)
  have h13 : Entails.eval a c372 := derived372 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c409 : DefaultClause 31 := directClause [(⟨28, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f409 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c405, some c403, some c394, some c408, some c10, some c153, some c56, some c92, some c182, some c16, some c113, some c72, some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p409 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked409 : lratChecker f409 p409 = .success := by decide +kernel
theorem unsat409 : Unsatisfiable (PosFin 31) f409 := by
  apply lratCheckerSound f409 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p409
  · intro a ha; simp [p409] at ha; subst a; trivial
  · exact checked409
theorem derived409 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c409 := by
  apply localUnsat_implies_entails f409 [c370, c405, c403, c394, c408, c10, c153, c56, c92, c182, c16, c113, c72] c409 unsat409 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c405 := derived405 a h
  have h2 : Entails.eval a c403 := derived403 a h
  have h3 : Entails.eval a c394 := derived394 a h
  have h4 : Entails.eval a c408 := derived408 a h
  have h5 : Entails.eval a c10 := h 9 (by decide)
  have h6 : Entails.eval a c153 := h 152 (by decide)
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c92 := h 91 (by decide)
  have h9 : Entails.eval a c182 := h 181 (by decide)
  have h10 : Entails.eval a c16 := h 15 (by decide)
  have h11 : Entails.eval a c113 := h 112 (by decide)
  have h12 : Entails.eval a c72 := h 71 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c410 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f410 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c403, some c394, some c113, some c5, some c147, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p410 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked410 : lratChecker f410 p410 = .success := by decide +kernel
theorem unsat410 : Unsatisfiable (PosFin 31) f410 := by
  apply lratCheckerSound f410 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p410
  · intro a ha; simp [p410] at ha; subst a; trivial
  · exact checked410
theorem derived410 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c410 := by
  apply localUnsat_implies_entails f410 [c409, c403, c394, c113, c5, c147] c410 unsat410 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c403 := derived403 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c113 := h 112 (by decide)
  have h4 : Entails.eval a c5 := h 4 (by decide)
  have h5 : Entails.eval a c147 := h 146 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c411 : DefaultClause 31 := directClause [(⟨4, by decide⟩, true), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f411 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c405, some c394, some c410, some c130, some c82, some c235, some c147, some c146, some c22, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p411 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked411 : lratChecker f411 p411 = .success := by decide +kernel
theorem unsat411 : Unsatisfiable (PosFin 31) f411 := by
  apply lratCheckerSound f411 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p411
  · intro a ha; simp [p411] at ha; subst a; trivial
  · exact checked411
theorem derived411 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c411 := by
  apply localUnsat_implies_entails f411 [c409, c405, c394, c410, c130, c82, c235, c147, c146, c22] c411 unsat411 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c405 := derived405 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c410 := derived410 a h
  have h4 : Entails.eval a c130 := h 129 (by decide)
  have h5 : Entails.eval a c82 := h 81 (by decide)
  have h6 : Entails.eval a c235 := h 234 (by decide)
  have h7 : Entails.eval a c147 := h 146 (by decide)
  have h8 : Entails.eval a c146 := h 145 (by decide)
  have h9 : Entails.eval a c22 := h 21 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c412 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨22, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f412 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c409, some c394, some c82, some c405, some c130, some c16, some c77, some c22, some c111, some c146, some c262, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p412 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked412 : lratChecker f412 p412 = .success := by decide +kernel
theorem unsat412 : Unsatisfiable (PosFin 31) f412 := by
  apply lratCheckerSound f412 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p412
  · intro a ha; simp [p412] at ha; subst a; trivial
  · exact checked412
theorem derived412 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c412 := by
  apply localUnsat_implies_entails f412 [c370, c409, c394, c82, c405, c130, c16, c77, c22, c111, c146, c262] c412 unsat412 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c409 := derived409 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c82 := h 81 (by decide)
  have h4 : Entails.eval a c405 := derived405 a h
  have h5 : Entails.eval a c130 := h 129 (by decide)
  have h6 : Entails.eval a c16 := h 15 (by decide)
  have h7 : Entails.eval a c77 := h 76 (by decide)
  have h8 : Entails.eval a c22 := h 21 (by decide)
  have h9 : Entails.eval a c111 := h 110 (by decide)
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c262 := h 261 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c413 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f413 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c409, some c405, some c394, some c130, some c82, some c16, some c77, some c412, some c70, some c52, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p413 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked413 : lratChecker f413 p413 = .success := by decide +kernel
theorem unsat413 : Unsatisfiable (PosFin 31) f413 := by
  apply lratCheckerSound f413 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p413
  · intro a ha; simp [p413] at ha; subst a; trivial
  · exact checked413
theorem derived413 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c413 := by
  apply localUnsat_implies_entails f413 [c409, c405, c394, c130, c82, c16, c77, c412, c70, c52] c413 unsat413 (by rfl) a
  have h0 : Entails.eval a c409 := derived409 a h
  have h1 : Entails.eval a c405 := derived405 a h
  have h2 : Entails.eval a c394 := derived394 a h
  have h3 : Entails.eval a c130 := h 129 (by decide)
  have h4 : Entails.eval a c82 := h 81 (by decide)
  have h5 : Entails.eval a c16 := h 15 (by decide)
  have h6 : Entails.eval a c77 := h 76 (by decide)
  have h7 : Entails.eval a c412 := derived412 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c52 := h 51 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c414 : DefaultClause 31 := directClause [(⟨11, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f414 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c394, some c403, some c409, some c411, some c413, some c113, some c72, some c147, some c50, some c224, some c7, some (DefaultClause.unit (⟨11, by decide⟩, false))]
def p414 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked414 : lratChecker f414 p414 = .success := by decide +kernel
theorem unsat414 : Unsatisfiable (PosFin 31) f414 := by
  apply lratCheckerSound f414 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p414
  · intro a ha; simp [p414] at ha; subst a; trivial
  · exact checked414
theorem derived414 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c414 := by
  apply localUnsat_implies_entails f414 [c370, c394, c403, c409, c411, c413, c113, c72, c147, c50, c224, c7] c414 unsat414 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c394 := derived394 a h
  have h2 : Entails.eval a c403 := derived403 a h
  have h3 : Entails.eval a c409 := derived409 a h
  have h4 : Entails.eval a c411 := derived411 a h
  have h5 : Entails.eval a c413 := derived413 a h
  have h6 : Entails.eval a c113 := h 112 (by decide)
  have h7 : Entails.eval a c72 := h 71 (by decide)
  have h8 : Entails.eval a c147 := h 146 (by decide)
  have h9 : Entails.eval a c50 := h 49 (by decide)
  have h10 : Entails.eval a c224 := h 223 (by decide)
  have h11 : Entails.eval a c7 := h 6 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c415 : DefaultClause 31 := directClause [(⟨18, by decide⟩, false), (⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f415 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c50, some c147, some c7, some c135, some c52, some c89, some c20, some c276, some c102, some c43, some c44, some c83, some c72, some c28, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p415 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked415 : lratChecker f415 p415 = .success := by decide +kernel
theorem unsat415 : Unsatisfiable (PosFin 31) f415 := by
  apply lratCheckerSound f415 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p415
  · intro a ha; simp [p415] at ha; subst a; trivial
  · exact checked415
theorem derived415 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c415 := by
  apply localUnsat_implies_entails f415 [c370, c50, c147, c7, c135, c52, c89, c20, c276, c102, c43, c44, c83, c72, c28] c415 unsat415 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c50 := h 49 (by decide)
  have h2 : Entails.eval a c147 := h 146 (by decide)
  have h3 : Entails.eval a c7 := h 6 (by decide)
  have h4 : Entails.eval a c135 := h 134 (by decide)
  have h5 : Entails.eval a c52 := h 51 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c20 := h 19 (by decide)
  have h8 : Entails.eval a c276 := h 275 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  have h10 : Entails.eval a c43 := h 42 (by decide)
  have h11 : Entails.eval a c44 := h 43 (by decide)
  have h12 : Entails.eval a c83 := h 82 (by decide)
  have h13 : Entails.eval a c72 := h 71 (by decide)
  have h14 : Entails.eval a c28 := h 27 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c416 : DefaultClause 31 := directClause [(⟨29, by decide⟩, false), (⟨22, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f416 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c414, some c50, some c415, some c66, some c102, some c20, some c25, some c189, some c17, some c215, some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p416 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked416 : lratChecker f416 p416 = .success := by decide +kernel
theorem unsat416 : Unsatisfiable (PosFin 31) f416 := by
  apply lratCheckerSound f416 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p416
  · intro a ha; simp [p416] at ha; subst a; trivial
  · exact checked416
theorem derived416 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c416 := by
  apply localUnsat_implies_entails f416 [c370, c414, c50, c415, c66, c102, c20, c25, c189, c17, c215] c416 unsat416 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c50 := h 49 (by decide)
  have h3 : Entails.eval a c415 := derived415 a h
  have h4 : Entails.eval a c66 := h 65 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c25 := h 24 (by decide)
  have h8 : Entails.eval a c189 := h 188 (by decide)
  have h9 : Entails.eval a c17 := h 16 (by decide)
  have h10 : Entails.eval a c215 := h 214 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c417 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f417 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c414, some c370, some c416, some c59, some c141, some c189, some c20, some c14, some c31, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p417 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked417 : lratChecker f417 p417 = .success := by decide +kernel
theorem unsat417 : Unsatisfiable (PosFin 31) f417 := by
  apply lratCheckerSound f417 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p417
  · intro a ha; simp [p417] at ha; subst a; trivial
  · exact checked417
theorem derived417 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c417 := by
  apply localUnsat_implies_entails f417 [c414, c370, c416, c59, c141, c189, c20, c14, c31] c417 unsat417 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c370 := derived370 a h
  have h2 : Entails.eval a c416 := derived416 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c20 := h 19 (by decide)
  have h7 : Entails.eval a c14 := h 13 (by decide)
  have h8 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c418 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨9, by decide⟩, true), (⟨18, by decide⟩, true), (⟨16, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f418 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c414, some c49, some c96, some c60, some c142, some c31, some c258, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p418 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked418 : lratChecker f418 p418 = .success := by decide +kernel
theorem unsat418 : Unsatisfiable (PosFin 31) f418 := by
  apply lratCheckerSound f418 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p418
  · intro a ha; simp [p418] at ha; subst a; trivial
  · exact checked418
theorem derived418 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c418 := by
  apply localUnsat_implies_entails f418 [c414, c49, c96, c60, c142, c31, c258] c418 unsat418 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c49 := h 48 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c142 := h 141 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c258 := h 257 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c419 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨12, by decide⟩, false), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f419 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c160, some c212, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p419 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked419 : lratChecker f419 p419 = .success := by decide +kernel
theorem unsat419 : Unsatisfiable (PosFin 31) f419 := by
  apply lratCheckerSound f419 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p419
  · intro a ha; simp [p419] at ha; subst a; trivial
  · exact checked419
theorem derived419 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c419 := by
  apply localUnsat_implies_entails f419 [c370, c160, c212] c419 unsat419 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c160 := h 159 (by decide)
  have h2 : Entails.eval a c212 := h 211 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c420 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false), (⟨25, by decide⟩, true), (⟨9, by decide⟩, true), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true), (⟨16, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f420 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c419, some c211, some c229, some c164, some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true))]
def p420 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked420 : lratChecker f420 p420 = .success := by decide +kernel
theorem unsat420 : Unsatisfiable (PosFin 31) f420 := by
  apply lratCheckerSound f420 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p420
  · intro a ha; simp [p420] at ha; subst a; trivial
  · exact checked420
theorem derived420 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c420 := by
  apply localUnsat_implies_entails f420 [c370, c419, c211, c229, c164] c420 unsat420 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c419 := derived419 a h
  have h2 : Entails.eval a c211 := h 210 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  have h4 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c421 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨9, by decide⟩, true), (⟨16, by decide⟩, false), (⟨12, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f421 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c420, some c159, some c235, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p421 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked421 : lratChecker f421 p421 = .success := by decide +kernel
theorem unsat421 : Unsatisfiable (PosFin 31) f421 := by
  apply lratCheckerSound f421 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p421
  · intro a ha; simp [p421] at ha; subst a; trivial
  · exact checked421
theorem derived421 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c421 := by
  apply localUnsat_implies_entails f421 [c370, c420, c159, c235] c421 unsat421 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c420 := derived420 a h
  have h2 : Entails.eval a c159 := h 158 (by decide)
  have h3 : Entails.eval a c235 := h 234 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c422 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨22, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f422 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c416, some c59, some c141, some c417, some c190, some c418, some c421, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p422 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked422 : lratChecker f422 p422 = .success := by decide +kernel
theorem unsat422 : Unsatisfiable (PosFin 31) f422 := by
  apply lratCheckerSound f422 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p422
  · intro a ha; simp [p422] at ha; subst a; trivial
  · exact checked422
theorem derived422 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c422 := by
  apply localUnsat_implies_entails f422 [c370, c416, c59, c141, c417, c190, c418, c421] c422 unsat422 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c416 := derived416 a h
  have h2 : Entails.eval a c59 := h 58 (by decide)
  have h3 : Entails.eval a c141 := h 140 (by decide)
  have h4 : Entails.eval a c417 := derived417 a h
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c418 := derived418 a h
  have h7 : Entails.eval a c421 := derived421 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c423 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false), (⟨22, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f423 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c414, some c416, some c59, some c141, some c190, some c419, some c421, some c96, some c60, some (DefaultClause.unit (⟨12, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p423 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked423 : lratChecker f423 p423 = .success := by decide +kernel
theorem unsat423 : Unsatisfiable (PosFin 31) f423 := by
  apply lratCheckerSound f423 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p423
  · intro a ha; simp [p423] at ha; subst a; trivial
  · exact checked423
theorem derived423 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c423 := by
  apply localUnsat_implies_entails f423 [c370, c414, c416, c59, c141, c190, c419, c421, c96, c60] c423 unsat423 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c416 := derived416 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c190 := h 189 (by decide)
  have h6 : Entails.eval a c419 := derived419 a h
  have h7 : Entails.eval a c421 := derived421 a h
  have h8 : Entails.eval a c96 := h 95 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c424 : DefaultClause 31 := directClause [(⟨22, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f424 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c414, some c416, some c59, some c141, some c189, some c422, some c423, some c20, some c49, some c96, some c119, some c69, some c47, some c91, some c80, some c241, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p424 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked424 : lratChecker f424 p424 = .success := by decide +kernel
theorem unsat424 : Unsatisfiable (PosFin 31) f424 := by
  apply lratCheckerSound f424 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p424
  · intro a ha; simp [p424] at ha; subst a; trivial
  · exact checked424
theorem derived424 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c424 := by
  apply localUnsat_implies_entails f424 [c370, c414, c416, c59, c141, c189, c422, c423, c20, c49, c96, c119, c69, c47, c91, c80, c241] c424 unsat424 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c416 := derived416 a h
  have h3 : Entails.eval a c59 := h 58 (by decide)
  have h4 : Entails.eval a c141 := h 140 (by decide)
  have h5 : Entails.eval a c189 := h 188 (by decide)
  have h6 : Entails.eval a c422 := derived422 a h
  have h7 : Entails.eval a c423 := derived423 a h
  have h8 : Entails.eval a c20 := h 19 (by decide)
  have h9 : Entails.eval a c49 := h 48 (by decide)
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c119 := h 118 (by decide)
  have h12 : Entails.eval a c69 := h 68 (by decide)
  have h13 : Entails.eval a c47 := h 46 (by decide)
  have h14 : Entails.eval a c91 := h 90 (by decide)
  have h15 : Entails.eval a c80 := h 79 (by decide)
  have h16 : Entails.eval a c241 := h 240 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c425 : DefaultClause 31 := directClause [(⟨12, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f425 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c414, some c370, some c424, some c118, some c20, some c116, some c50, some c60, some c95, some c142, some c194, some (DefaultClause.unit (⟨12, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p425 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked425 : lratChecker f425 p425 = .success := by decide +kernel
theorem unsat425 : Unsatisfiable (PosFin 31) f425 := by
  apply lratCheckerSound f425 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p425
  · intro a ha; simp [p425] at ha; subst a; trivial
  · exact checked425
theorem derived425 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c425 := by
  apply localUnsat_implies_entails f425 [c414, c370, c424, c118, c20, c116, c50, c60, c95, c142, c194] c425 unsat425 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c370 := derived370 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c20 := h 19 (by decide)
  have h5 : Entails.eval a c116 := h 115 (by decide)
  have h6 : Entails.eval a c50 := h 49 (by decide)
  have h7 : Entails.eval a c60 := h 59 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c142 := h 141 (by decide)
  have h10 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c426 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f426 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c414, some c370, some c425, some c424, some c49, some c50, some c96, some c38, some c95, some c60, some c77, some c419, some c142, some c254, some c237, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p426 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked426 : lratChecker f426 p426 = .success := by decide +kernel
theorem unsat426 : Unsatisfiable (PosFin 31) f426 := by
  apply lratCheckerSound f426 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p426
  · intro a ha; simp [p426] at ha; subst a; trivial
  · exact checked426
theorem derived426 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c426 := by
  apply localUnsat_implies_entails f426 [c414, c370, c425, c424, c49, c50, c96, c38, c95, c60, c77, c419, c142, c254, c237] c426 unsat426 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c370 := derived370 a h
  have h2 : Entails.eval a c425 := derived425 a h
  have h3 : Entails.eval a c424 := derived424 a h
  have h4 : Entails.eval a c49 := h 48 (by decide)
  have h5 : Entails.eval a c50 := h 49 (by decide)
  have h6 : Entails.eval a c96 := h 95 (by decide)
  have h7 : Entails.eval a c38 := h 37 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c77 := h 76 (by decide)
  have h11 : Entails.eval a c419 := derived419 a h
  have h12 : Entails.eval a c142 := h 141 (by decide)
  have h13 : Entails.eval a c254 := h 253 (by decide)
  have h14 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c427 : DefaultClause 31 := directClause [(⟨5, by decide⟩, true), (⟨16, by decide⟩, true), (⟨29, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f427 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c414, some c370, some c424, some c118, some c426, some c103, some c425, some c130, some c157, some c257, some c256, some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p427 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked427 : lratChecker f427 p427 = .success := by decide +kernel
theorem unsat427 : Unsatisfiable (PosFin 31) f427 := by
  apply lratCheckerSound f427 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p427
  · intro a ha; simp [p427] at ha; subst a; trivial
  · exact checked427
theorem derived427 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c427 := by
  apply localUnsat_implies_entails f427 [c414, c370, c424, c118, c426, c103, c425, c130, c157, c257, c256] c427 unsat427 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c370 := derived370 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c425 := derived425 a h
  have h7 : Entails.eval a c130 := h 129 (by decide)
  have h8 : Entails.eval a c157 := h 156 (by decide)
  have h9 : Entails.eval a c257 := h 256 (by decide)
  have h10 : Entails.eval a c256 := h 255 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c428 : DefaultClause 31 := directClause [(⟨17, by decide⟩, false), (⟨29, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f428 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c414, some c424, some c95, some c425, some c419, some c427, some c209, some c208, some c219, some c15, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p428 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked428 : lratChecker f428 p428 = .success := by decide +kernel
theorem unsat428 : Unsatisfiable (PosFin 31) f428 := by
  apply lratCheckerSound f428 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p428
  · intro a ha; simp [p428] at ha; subst a; trivial
  · exact checked428
theorem derived428 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c428 := by
  apply localUnsat_implies_entails f428 [c370, c414, c424, c95, c425, c419, c427, c209, c208, c219, c15] c428 unsat428 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c95 := h 94 (by decide)
  have h4 : Entails.eval a c425 := derived425 a h
  have h5 : Entails.eval a c419 := derived419 a h
  have h6 : Entails.eval a c427 := derived427 a h
  have h7 : Entails.eval a c209 := h 208 (by decide)
  have h8 : Entails.eval a c208 := h 207 (by decide)
  have h9 : Entails.eval a c219 := h 218 (by decide)
  have h10 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c429 : DefaultClause 31 := directClause [(⟨29, by decide⟩, true), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f429 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c414, some c370, some c424, some c118, some c426, some c103, some c425, some c130, some c95, some c428, some c87, some c82, some c256, some c28, some c251, some c179, some c40, some c123, some c164, some c121, some c203, some (DefaultClause.unit (⟨29, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p429 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked429 : lratChecker f429 p429 = .success := by decide +kernel
theorem unsat429 : Unsatisfiable (PosFin 31) f429 := by
  apply lratCheckerSound f429 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p429
  · intro a ha; simp [p429] at ha; subst a; trivial
  · exact checked429
theorem derived429 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c429 := by
  apply localUnsat_implies_entails f429 [c414, c370, c424, c118, c426, c103, c425, c130, c95, c428, c87, c82, c256, c28, c251, c179, c40, c123, c164, c121, c203] c429 unsat429 (by rfl) a
  have h0 : Entails.eval a c414 := derived414 a h
  have h1 : Entails.eval a c370 := derived370 a h
  have h2 : Entails.eval a c424 := derived424 a h
  have h3 : Entails.eval a c118 := h 117 (by decide)
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c425 := derived425 a h
  have h7 : Entails.eval a c130 := h 129 (by decide)
  have h8 : Entails.eval a c95 := h 94 (by decide)
  have h9 : Entails.eval a c428 := derived428 a h
  have h10 : Entails.eval a c87 := h 86 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c256 := h 255 (by decide)
  have h13 : Entails.eval a c28 := h 27 (by decide)
  have h14 : Entails.eval a c251 := h 250 (by decide)
  have h15 : Entails.eval a c179 := h 178 (by decide)
  have h16 : Entails.eval a c40 := h 39 (by decide)
  have h17 : Entails.eval a c123 := h 122 (by decide)
  have h18 : Entails.eval a c164 := h 163 (by decide)
  have h19 : Entails.eval a c121 := h 120 (by decide)
  have h20 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c430 : DefaultClause 31 := directClause [(⟨22, by decide⟩, false), (⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f430 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c414, some c118, some c425, some c426, some c103, some c429, some c102, some c66, some c69, some c147, some c82, some c273, some c259, some c158, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p430 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked430 : lratChecker f430 p430 = .success := by decide +kernel
theorem unsat430 : Unsatisfiable (PosFin 31) f430 := by
  apply lratCheckerSound f430 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p430
  · intro a ha; simp [p430] at ha; subst a; trivial
  · exact checked430
theorem derived430 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c430 := by
  apply localUnsat_implies_entails f430 [c370, c414, c118, c425, c426, c103, c429, c102, c66, c69, c147, c82, c273, c259, c158] c430 unsat430 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c118 := h 117 (by decide)
  have h3 : Entails.eval a c425 := derived425 a h
  have h4 : Entails.eval a c426 := derived426 a h
  have h5 : Entails.eval a c103 := h 102 (by decide)
  have h6 : Entails.eval a c429 := derived429 a h
  have h7 : Entails.eval a c102 := h 101 (by decide)
  have h8 : Entails.eval a c66 := h 65 (by decide)
  have h9 : Entails.eval a c69 := h 68 (by decide)
  have h10 : Entails.eval a c147 := h 146 (by decide)
  have h11 : Entails.eval a c82 := h 81 (by decide)
  have h12 : Entails.eval a c273 := h 272 (by decide)
  have h13 : Entails.eval a c259 := h 258 (by decide)
  have h14 : Entails.eval a c158 := h 157 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c431 : DefaultClause 31 := directClause [(⟨28, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f431 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c424, some c430, some (DefaultClause.unit (⟨28, by decide⟩, true))]
def p431 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2]]
theorem checked431 : lratChecker f431 p431 = .success := by decide +kernel
theorem unsat431 : Unsatisfiable (PosFin 31) f431 := by
  apply lratCheckerSound f431 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p431
  · intro a ha; simp [p431] at ha; subst a; trivial
  · exact checked431
theorem derived431 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c431 := by
  apply localUnsat_implies_entails f431 [c424, c430] c431 unsat431 (by rfl) a
  have h0 : Entails.eval a c424 := derived424 a h
  have h1 : Entails.eval a c430 := derived430 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c432 : DefaultClause 31 := directClause [(⟨23, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f432 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c431, some c414, some c370, some c98, some (DefaultClause.unit (⟨23, by decide⟩, true))]
def p432 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked432 : lratChecker f432 p432 = .success := by decide +kernel
theorem unsat432 : Unsatisfiable (PosFin 31) f432 := by
  apply lratCheckerSound f432 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p432
  · intro a ha; simp [p432] at ha; subst a; trivial
  · exact checked432
theorem derived432 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c432 := by
  apply localUnsat_implies_entails f432 [c431, c414, c370, c98] c432 unsat432 (by rfl) a
  have h0 : Entails.eval a c431 := derived431 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c98 := h 97 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c433 : DefaultClause 31 := directClause [(⟨17, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f433 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c432, some c431, some c370, some c62, some (DefaultClause.unit (⟨17, by decide⟩, false))]
def p433 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked433 : lratChecker f433 p433 = .success := by decide +kernel
theorem unsat433 : Unsatisfiable (PosFin 31) f433 := by
  apply lratCheckerSound f433 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p433
  · intro a ha; simp [p433] at ha; subst a; trivial
  · exact checked433
theorem derived433 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c433 := by
  apply localUnsat_implies_entails f433 [c432, c431, c370, c62] c433 unsat433 (by rfl) a
  have h0 : Entails.eval a c432 := derived432 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c62 := h 61 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c434 : DefaultClause 31 := directClause [(⟨5, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f434 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c433, some c431, some c370, some c144, some (DefaultClause.unit (⟨5, by decide⟩, true))]
def p434 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked434 : lratChecker f434 p434 = .success := by decide +kernel
theorem unsat434 : Unsatisfiable (PosFin 31) f434 := by
  apply lratCheckerSound f434 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p434
  · intro a ha; simp [p434] at ha; subst a; trivial
  · exact checked434
theorem derived434 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c434 := by
  apply localUnsat_implies_entails f434 [c433, c431, c370, c144] c434 unsat434 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c435 : DefaultClause 31 := directClause [(⟨15, by decide⟩, true), (⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f435 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c432, some c434, some c370, some c431, some c56, some c256, some c92, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p435 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked435 : lratChecker f435 p435 = .success := by decide +kernel
theorem unsat435 : Unsatisfiable (PosFin 31) f435 := by
  apply lratCheckerSound f435 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p435
  · intro a ha; simp [p435] at ha; subst a; trivial
  · exact checked435
theorem derived435 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c435 := by
  apply localUnsat_implies_entails f435 [c432, c434, c370, c431, c56, c256, c92] c435 unsat435 (by rfl) a
  have h0 : Entails.eval a c432 := derived432 a h
  have h1 : Entails.eval a c434 := derived434 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c431 := derived431 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c256 := h 255 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c436 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨18, by decide⟩, false), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f436 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c431, some c370, some c434, some c435, some c37, some c138, some c170, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p436 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked436 : lratChecker f436 p436 = .success := by decide +kernel
theorem unsat436 : Unsatisfiable (PosFin 31) f436 := by
  apply lratCheckerSound f436 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p436
  · intro a ha; simp [p436] at ha; subst a; trivial
  · exact checked436
theorem derived436 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c436 := by
  apply localUnsat_implies_entails f436 [c431, c370, c434, c435, c37, c138, c170] c436 unsat436 (by rfl) a
  have h0 : Entails.eval a c431 := derived431 a h
  have h1 : Entails.eval a c370 := derived370 a h
  have h2 : Entails.eval a c434 := derived434 a h
  have h3 : Entails.eval a c435 := derived435 a h
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c138 := h 137 (by decide)
  have h6 : Entails.eval a c170 := h 169 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c437 : DefaultClause 31 := directClause [(⟨25, by decide⟩, false), (⟨29, by decide⟩, false), (⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f437 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c433, some c432, some c434, some c431, some c193, some c419, some c57, some c93, some c48, some c21, some (DefaultClause.unit (⟨25, by decide⟩, true)), some (DefaultClause.unit (⟨29, by decide⟩, true)), some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p437 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked437 : lratChecker f437 p437 = .success := by decide +kernel
theorem unsat437 : Unsatisfiable (PosFin 31) f437 := by
  apply lratCheckerSound f437 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p437
  · intro a ha; simp [p437] at ha; subst a; trivial
  · exact checked437
theorem derived437 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c437 := by
  apply localUnsat_implies_entails f437 [c433, c432, c434, c431, c193, c419, c57, c93, c48, c21] c437 unsat437 (by rfl) a
  have h0 : Entails.eval a c433 := derived433 a h
  have h1 : Entails.eval a c432 := derived432 a h
  have h2 : Entails.eval a c434 := derived434 a h
  have h3 : Entails.eval a c431 := derived431 a h
  have h4 : Entails.eval a c193 := h 192 (by decide)
  have h5 : Entails.eval a c419 := derived419 a h
  have h6 : Entails.eval a c57 := h 56 (by decide)
  have h7 : Entails.eval a c93 := h 92 (by decide)
  have h8 : Entails.eval a c48 := h 47 (by decide)
  have h9 : Entails.eval a c21 := h 20 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c438 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true), (⟨3, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f438 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c434, some c386, some c151, some c85, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p438 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked438 : lratChecker f438 p438 = .success := by decide +kernel
theorem unsat438 : Unsatisfiable (PosFin 31) f438 := by
  apply lratCheckerSound f438 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p438
  · intro a ha; simp [p438] at ha; subst a; trivial
  · exact checked438
theorem derived438 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c438 := by
  apply localUnsat_implies_entails f438 [c434, c386, c151, c85] c438 unsat438 (by rfl) a
  have h0 : Entails.eval a c434 := derived434 a h
  have h1 : Entails.eval a c386 := derived386 a h
  have h2 : Entails.eval a c151 := h 150 (by decide)
  have h3 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c439 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true), (⟨16, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f439 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c370, some c431, some c435, some c436, some c138, some c438, some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, false))]
def p439 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked439 : lratChecker f439 p439 = .success := by decide +kernel
theorem unsat439 : Unsatisfiable (PosFin 31) f439 := by
  apply lratCheckerSound f439 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p439
  · intro a ha; simp [p439] at ha; subst a; trivial
  · exact checked439
theorem derived439 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c439 := by
  apply localUnsat_implies_entails f439 [c370, c431, c435, c436, c138, c438] c439 unsat439 (by rfl) a
  have h0 : Entails.eval a c370 := derived370 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c435 := derived435 a h
  have h3 : Entails.eval a c436 := derived436 a h
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c438 := derived438 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c440 : DefaultClause 31 := directClause [(⟨12, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f440 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c432, some c434, some c370, some c433, some c419, some c193, some c439, some c437, some c59, some c11, some c95, some c210, some c15, some (DefaultClause.unit (⟨12, by decide⟩, true))]
def p440 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked440 : lratChecker f440 p440 = .success := by decide +kernel
theorem unsat440 : Unsatisfiable (PosFin 31) f440 := by
  apply lratCheckerSound f440 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p440
  · intro a ha; simp [p440] at ha; subst a; trivial
  · exact checked440
theorem derived440 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c440 := by
  apply localUnsat_implies_entails f440 [c432, c434, c370, c433, c419, c193, c439, c437, c59, c11, c95, c210, c15] c440 unsat440 (by rfl) a
  have h0 : Entails.eval a c432 := derived432 a h
  have h1 : Entails.eval a c434 := derived434 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c433 := derived433 a h
  have h4 : Entails.eval a c419 := derived419 a h
  have h5 : Entails.eval a c193 := h 192 (by decide)
  have h6 : Entails.eval a c439 := derived439 a h
  have h7 : Entails.eval a c437 := derived437 a h
  have h8 : Entails.eval a c59 := h 58 (by decide)
  have h9 : Entails.eval a c11 := h 10 (by decide)
  have h10 : Entails.eval a c95 := h 94 (by decide)
  have h11 : Entails.eval a c210 := h 209 (by decide)
  have h12 : Entails.eval a c15 := h 14 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c441 : DefaultClause 31 := directClause [(⟨10, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f441 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c440, some c431, some c370, some c23, some (DefaultClause.unit (⟨10, by decide⟩, false))]
def p441 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked441 : lratChecker f441 p441 = .success := by decide +kernel
theorem unsat441 : Unsatisfiable (PosFin 31) f441 := by
  apply lratCheckerSound f441 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p441
  · intro a ha; simp [p441] at ha; subst a; trivial
  · exact checked441
theorem derived441 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c441 := by
  apply localUnsat_implies_entails f441 [c440, c431, c370, c23] c441 unsat441 (by rfl) a
  have h0 : Entails.eval a c440 := derived440 a h
  have h1 : Entails.eval a c431 := derived431 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c23 := h 22 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c442 : DefaultClause 31 := directClause [(⟨7, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f442 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c441, some c414, some c25, some (DefaultClause.unit (⟨7, by decide⟩, true))]
def p442 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked442 : lratChecker f442 p442 = .success := by decide +kernel
theorem unsat442 : Unsatisfiable (PosFin 31) f442 := by
  apply lratCheckerSound f442 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p442
  · intro a ha; simp [p442] at ha; subst a; trivial
  · exact checked442
theorem derived442 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c442 := by
  apply localUnsat_implies_entails f442 [c441, c414, c25] c442 unsat442 (by rfl) a
  have h0 : Entails.eval a c441 := derived441 a h
  have h1 : Entails.eval a c414 := derived414 a h
  have h2 : Entails.eval a c25 := h 24 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c443 : DefaultClause 31 := directClause [(⟨25, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f443 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c442, some c440, some c370, some c20, some (DefaultClause.unit (⟨25, by decide⟩, false))]
def p443 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked443 : lratChecker f443 p443 = .success := by decide +kernel
theorem unsat443 : Unsatisfiable (PosFin 31) f443 := by
  apply lratCheckerSound f443 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p443
  · intro a ha; simp [p443] at ha; subst a; trivial
  · exact checked443
theorem derived443 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c443 := by
  apply localUnsat_implies_entails f443 [c442, c440, c370, c20] c443 unsat443 (by rfl) a
  have h0 : Entails.eval a c442 := derived442 a h
  have h1 : Entails.eval a c440 := derived440 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c20 := h 19 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c444 : DefaultClause 31 := directClause [(⟨19, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f444 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c443, some c441, some c414, some c131, some (DefaultClause.unit (⟨19, by decide⟩, true))]
def p444 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked444 : lratChecker f444 p444 = .success := by decide +kernel
theorem unsat444 : Unsatisfiable (PosFin 31) f444 := by
  apply lratCheckerSound f444 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p444
  · intro a ha; simp [p444] at ha; subst a; trivial
  · exact checked444
theorem derived444 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c444 := by
  apply localUnsat_implies_entails f444 [c443, c441, c414, c131] c444 unsat444 (by rfl) a
  have h0 : Entails.eval a c443 := derived443 a h
  have h1 : Entails.eval a c441 := derived441 a h
  have h2 : Entails.eval a c414 := derived414 a h
  have h3 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c445 : DefaultClause 31 := directClause [(⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f445 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c444, some c441, some c414, some c184, some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p445 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked445 : lratChecker f445 p445 = .success := by decide +kernel
theorem unsat445 : Unsatisfiable (PosFin 31) f445 := by
  apply lratCheckerSound f445 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p445
  · intro a ha; simp [p445] at ha; subst a; trivial
  · exact checked445
theorem derived445 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c445 := by
  apply localUnsat_implies_entails f445 [c444, c441, c414, c184] c445 unsat445 (by rfl) a
  have h0 : Entails.eval a c444 := derived444 a h
  have h1 : Entails.eval a c441 := derived441 a h
  have h2 : Entails.eval a c414 := derived414 a h
  have h3 : Entails.eval a c184 := h 183 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c446 : DefaultClause 31 := directClause [(⟨13, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f446 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c445, some c441, some c414, some c213, some (DefaultClause.unit (⟨13, by decide⟩, true))]
def p446 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked446 : lratChecker f446 p446 = .success := by decide +kernel
theorem unsat446 : Unsatisfiable (PosFin 31) f446 := by
  apply lratCheckerSound f446 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p446
  · intro a ha; simp [p446] at ha; subst a; trivial
  · exact checked446
theorem derived446 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c446 := by
  apply localUnsat_implies_entails f446 [c445, c441, c414, c213] c446 unsat446 (by rfl) a
  have h0 : Entails.eval a c445 := derived445 a h
  have h1 : Entails.eval a c441 := derived441 a h
  have h2 : Entails.eval a c414 := derived414 a h
  have h3 : Entails.eval a c213 := h 212 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c447 : DefaultClause 31 := directClause [(⟨18, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f447 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c446, some c440, some c442, some c14, some (DefaultClause.unit (⟨18, by decide⟩, false))]
def p447 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked447 : lratChecker f447 p447 = .success := by decide +kernel
theorem unsat447 : Unsatisfiable (PosFin 31) f447 := by
  apply lratCheckerSound f447 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p447
  · intro a ha; simp [p447] at ha; subst a; trivial
  · exact checked447
theorem derived447 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c447 := by
  apply localUnsat_implies_entails f447 [c446, c440, c442, c14] c447 unsat447 (by rfl) a
  have h0 : Entails.eval a c446 := derived446 a h
  have h1 : Entails.eval a c440 := derived440 a h
  have h2 : Entails.eval a c442 := derived442 a h
  have h3 : Entails.eval a c14 := h 13 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c448 : DefaultClause 31 := directClause [(⟨3, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f448 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c446, some c440, some c370, some c444, some c434, some c265, some (DefaultClause.unit (⟨3, by decide⟩, false))]
def p448 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked448 : lratChecker f448 p448 = .success := by decide +kernel
theorem unsat448 : Unsatisfiable (PosFin 31) f448 := by
  apply lratCheckerSound f448 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p448
  · intro a ha; simp [p448] at ha; subst a; trivial
  · exact checked448
theorem derived448 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c448 := by
  apply localUnsat_implies_entails f448 [c446, c440, c370, c444, c434, c265] c448 unsat448 (by rfl) a
  have h0 : Entails.eval a c446 := derived446 a h
  have h1 : Entails.eval a c440 := derived440 a h
  have h2 : Entails.eval a c370 := derived370 a h
  have h3 : Entails.eval a c444 := derived444 a h
  have h4 : Entails.eval a c434 := derived434 a h
  have h5 : Entails.eval a c265 := h 264 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c449 : DefaultClause 31 := directClause [(⟨6, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f449 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c447, some c441, some c414, some c223, some (DefaultClause.unit (⟨6, by decide⟩, true))]
def p449 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked449 : lratChecker f449 p449 = .success := by decide +kernel
theorem unsat449 : Unsatisfiable (PosFin 31) f449 := by
  apply lratCheckerSound f449 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p449
  · intro a ha; simp [p449] at ha; subst a; trivial
  · exact checked449
theorem derived449 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c449 := by
  apply localUnsat_implies_entails f449 [c447, c441, c414, c223] c449 unsat449 (by rfl) a
  have h0 : Entails.eval a c447 := derived447 a h
  have h1 : Entails.eval a c441 := derived441 a h
  have h2 : Entails.eval a c414 := derived414 a h
  have h3 : Entails.eval a c223 := h 222 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c450 : DefaultClause 31 := directClause [(⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f450 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c448, some c445, some c12, some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p450 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked450 : lratChecker f450 p450 = .success := by decide +kernel
theorem unsat450 : Unsatisfiable (PosFin 31) f450 := by
  apply lratCheckerSound f450 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p450
  · intro a ha; simp [p450] at ha; subst a; trivial
  · exact checked450
theorem derived450 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c450 := by
  apply localUnsat_implies_entails f450 [c448, c445, c12] c450 unsat450 (by rfl) a
  have h0 : Entails.eval a c448 := derived448 a h
  have h1 : Entails.eval a c445 := derived445 a h
  have h2 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c451 : DefaultClause 31 := directClause [] (by decide +kernel) (by decide +kernel)
def f451 : DefaultFormula 31 := DefaultFormula.ofArray #[none, some c449, some c450, some c431, some c370, some c10]
def p451 : List (Action (DefaultClause 31) (PosFin 31)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked451 : lratChecker f451 p451 = .success := by decide +kernel
theorem unsat451 : Unsatisfiable (PosFin 31) f451 := by
  apply lratCheckerSound f451 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p451
  · intro a ha; simp [p451] at ha; subst a; trivial
  · exact checked451
theorem derived451 (a : PosFin 31 → Bool) (h : InputSat a) : Entails.eval a c451 := by
  apply localUnsat_implies_entails f451 [c449, c450, c431, c370, c10] c451 unsat451 (by rfl) a
  have h0 : Entails.eval a c449 := derived449 a h
  have h1 : Entails.eval a c450 := derived450 a h
  have h2 : Entails.eval a c431 := derived431 a h
  have h3 : Entails.eval a c370 := derived370 a h
  have h4 : Entails.eval a c10 := h 9 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived451

end CochromaticTwenty.Certificates.Z12Direct_5_8_2
