import MerLeanExperiment.Certificates.B16_0_1.Steps0100_0199

/-! Generated from the actual pinned b16_0_1-trim CNF/LRAT data.
The generator is untrusted: every computation and inference is kernel checked. -/
namespace CochromaticTwenty.Certificates.B16_0_1
open Std.Sat Std.Tactic.BVDecide.LRAT Std.Tactic.BVDecide.LRAT.Internal
open CochromaticTwenty.CertificateKernel
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def c527 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨36, by decide⟩, true), (⟨35, by decide⟩, true), (⟨33, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f527 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c227, some c247, some c283, some c321, some c226, some c285, some c203, some c294, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p527 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked527 : lratChecker f527 p527 = .success := by decide +kernel
theorem unsat527 : Unsatisfiable (PosFin 57) f527 := by
  apply lratCheckerSound f527 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p527
  · intro a ha; simp [p527] at ha; subst a; trivial
  · exact checked527
theorem derived527 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c527 := by
  apply localUnsat_implies_entails f527 [c227, c247, c283, c321, c226, c285, c203, c294] c527 unsat527 (by rfl) a
  have h0 : Entails.eval a c227 := h 226 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c283 := h 282 (by decide)
  have h3 : Entails.eval a c321 := h 320 (by decide)
  have h4 : Entails.eval a c226 := h 225 (by decide)
  have h5 : Entails.eval a c285 := h 284 (by decide)
  have h6 : Entails.eval a c203 := h 202 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c528 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨35, by decide⟩, true), (⟨50, by decide⟩, false), (⟨33, by decide⟩, false), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f528 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c527, some c202, some c245, some c226, some c204, some c283, some c462, some c323, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p528 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked528 : lratChecker f528 p528 = .success := by decide +kernel
theorem unsat528 : Unsatisfiable (PosFin 57) f528 := by
  apply lratCheckerSound f528 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p528
  · intro a ha; simp [p528] at ha; subst a; trivial
  · exact checked528
theorem derived528 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c528 := by
  apply localUnsat_implies_entails f528 [c527, c202, c245, c226, c204, c283, c462, c323] c528 unsat528 (by rfl) a
  have h0 : Entails.eval a c527 := derived527 a h
  have h1 : Entails.eval a c202 := h 201 (by decide)
  have h2 : Entails.eval a c245 := h 244 (by decide)
  have h3 : Entails.eval a c226 := h 225 (by decide)
  have h4 : Entails.eval a c204 := h 203 (by decide)
  have h5 : Entails.eval a c283 := h 282 (by decide)
  have h6 : Entails.eval a c462 := derived462 a h
  have h7 : Entails.eval a c323 := h 322 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c529 : DefaultClause 57 := directClause [(⟨1, by decide⟩, true), (⟨2, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f529 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c511, some c20, some c55, some c62, some c526, some c64, some c291, some c293, some c528, some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p529 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked529 : lratChecker f529 p529 = .success := by decide +kernel
theorem unsat529 : Unsatisfiable (PosFin 57) f529 := by
  apply lratCheckerSound f529 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p529
  · intro a ha; simp [p529] at ha; subst a; trivial
  · exact checked529
theorem derived529 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c529 := by
  apply localUnsat_implies_entails f529 [c511, c20, c55, c62, c526, c64, c291, c293, c528] c529 unsat529 (by rfl) a
  have h0 : Entails.eval a c511 := derived511 a h
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c55 := h 54 (by decide)
  have h3 : Entails.eval a c62 := h 61 (by decide)
  have h4 : Entails.eval a c526 := derived526 a h
  have h5 : Entails.eval a c64 := h 63 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c293 := h 292 (by decide)
  have h8 : Entails.eval a c528 := derived528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c530 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f530 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c291, some c528, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p530 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked530 : lratChecker f530 p530 = .success := by decide +kernel
theorem unsat530 : Unsatisfiable (PosFin 57) f530 := by
  apply lratCheckerSound f530 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p530
  · intro a ha; simp [p530] at ha; subst a; trivial
  · exact checked530
theorem derived530 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c530 := by
  apply localUnsat_implies_entails f530 [c291, c528] c530 unsat530 (by rfl) a
  have h0 : Entails.eval a c291 := h 290 (by decide)
  have h1 : Entails.eval a c528 := derived528 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c531 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨35, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f531 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c530, some c92, some c93, some c202, some c244, some c245, some c226, some c204, some c56, some c283, some c90, some c323, some c34, some c7, some c36, some c284, some c88, some c151, some c240, some c17, some c200, some c150, some c175, some c106, some c105, some c49, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p531 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked531 : lratChecker f531 p531 = .success := by decide +kernel
theorem unsat531 : Unsatisfiable (PosFin 57) f531 := by
  apply lratCheckerSound f531 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p531
  · intro a ha; simp [p531] at ha; subst a; trivial
  · exact checked531
theorem derived531 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c531 := by
  apply localUnsat_implies_entails f531 [c530, c92, c93, c202, c244, c245, c226, c204, c56, c283, c90, c323, c34, c7, c36, c284, c88, c151, c240, c17, c200, c150, c175, c106, c105, c49] c531 unsat531 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c202 := h 201 (by decide)
  have h4 : Entails.eval a c244 := h 243 (by decide)
  have h5 : Entails.eval a c245 := h 244 (by decide)
  have h6 : Entails.eval a c226 := h 225 (by decide)
  have h7 : Entails.eval a c204 := h 203 (by decide)
  have h8 : Entails.eval a c56 := h 55 (by decide)
  have h9 : Entails.eval a c283 := h 282 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c323 := h 322 (by decide)
  have h12 : Entails.eval a c34 := h 33 (by decide)
  have h13 : Entails.eval a c7 := h 6 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c284 := h 283 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c151 := h 150 (by decide)
  have h18 : Entails.eval a c240 := h 239 (by decide)
  have h19 : Entails.eval a c17 := h 16 (by decide)
  have h20 : Entails.eval a c200 := h 199 (by decide)
  have h21 : Entails.eval a c150 := h 149 (by decide)
  have h22 : Entails.eval a c175 := h 174 (by decide)
  have h23 : Entails.eval a c106 := h 105 (by decide)
  have h24 : Entails.eval a c105 := h 104 (by decide)
  have h25 : Entails.eval a c49 := h 48 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c532 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f532 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c530, some c92, some c93, some c531, some c246, some c227, some c247, some c283, some c33, some c35, some c6, some c24, some c321, some c226, some c242, some c285, some c21, some c200, some c151, some c90, some c18, some c89, some c150, some c377, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p532 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked532 : lratChecker f532 p532 = .success := by decide +kernel
theorem unsat532 : Unsatisfiable (PosFin 57) f532 := by
  apply lratCheckerSound f532 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p532
  · intro a ha; simp [p532] at ha; subst a; trivial
  · exact checked532
theorem derived532 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c532 := by
  apply localUnsat_implies_entails f532 [c530, c92, c93, c531, c246, c227, c247, c283, c33, c35, c6, c24, c321, c226, c242, c285, c21, c200, c151, c90, c18, c89, c150, c377] c532 unsat532 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c93 := h 92 (by decide)
  have h3 : Entails.eval a c531 := derived531 a h
  have h4 : Entails.eval a c246 := h 245 (by decide)
  have h5 : Entails.eval a c227 := h 226 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  have h7 : Entails.eval a c283 := h 282 (by decide)
  have h8 : Entails.eval a c33 := h 32 (by decide)
  have h9 : Entails.eval a c35 := h 34 (by decide)
  have h10 : Entails.eval a c6 := h 5 (by decide)
  have h11 : Entails.eval a c24 := h 23 (by decide)
  have h12 : Entails.eval a c321 := h 320 (by decide)
  have h13 : Entails.eval a c226 := h 225 (by decide)
  have h14 : Entails.eval a c242 := h 241 (by decide)
  have h15 : Entails.eval a c285 := h 284 (by decide)
  have h16 : Entails.eval a c21 := h 20 (by decide)
  have h17 : Entails.eval a c200 := h 199 (by decide)
  have h18 : Entails.eval a c151 := h 150 (by decide)
  have h19 : Entails.eval a c90 := h 89 (by decide)
  have h20 : Entails.eval a c18 := h 17 (by decide)
  have h21 : Entails.eval a c89 := h 88 (by decide)
  have h22 : Entails.eval a c150 := h 149 (by decide)
  have h23 : Entails.eval a c377 := derived377 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c533 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨37, by decide⟩, true), (⟨33, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨18, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f533 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c246, some c247, some c200, some c35, some c242, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, true))]
def p533 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked533 : lratChecker f533 p533 = .success := by decide +kernel
theorem unsat533 : Unsatisfiable (PosFin 57) f533 := by
  apply lratCheckerSound f533 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p533
  · intro a ha; simp [p533] at ha; subst a; trivial
  · exact checked533
theorem derived533 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c533 := by
  apply localUnsat_implies_entails f533 [c246, c247, c200, c35, c242] c533 unsat533 (by rfl) a
  have h0 : Entails.eval a c246 := h 245 (by decide)
  have h1 : Entails.eval a c247 := h 246 (by decide)
  have h2 : Entails.eval a c200 := h 199 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c242 := h 241 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c534 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨3, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, false), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨20, by decide⟩, true), (⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f534 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c151, some c18, some c146, some c104, some c113, some c260, some c47, some c189, some c132, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p534 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked534 : lratChecker f534 p534 = .success := by decide +kernel
theorem unsat534 : Unsatisfiable (PosFin 57) f534 := by
  apply lratCheckerSound f534 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p534
  · intro a ha; simp [p534] at ha; subst a; trivial
  · exact checked534
theorem derived534 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c534 := by
  apply localUnsat_implies_entails f534 [c151, c18, c146, c104, c113, c260, c47, c189, c132] c534 unsat534 (by rfl) a
  have h0 : Entails.eval a c151 := h 150 (by decide)
  have h1 : Entails.eval a c18 := h 17 (by decide)
  have h2 : Entails.eval a c146 := h 145 (by decide)
  have h3 : Entails.eval a c104 := h 103 (by decide)
  have h4 : Entails.eval a c113 := h 112 (by decide)
  have h5 : Entails.eval a c260 := h 259 (by decide)
  have h6 : Entails.eval a c47 := h 46 (by decide)
  have h7 : Entails.eval a c189 := h 188 (by decide)
  have h8 : Entails.eval a c132 := h 131 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c535 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨19, by decide⟩, true), (⟨5, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f535 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c530, some c300, some c533, some c6, some c24, some c31, some c90, some c534, some c204, some c60, some c230, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p535 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked535 : lratChecker f535 p535 = .success := by decide +kernel
theorem unsat535 : Unsatisfiable (PosFin 57) f535 := by
  apply lratCheckerSound f535 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p535
  · intro a ha; simp [p535] at ha; subst a; trivial
  · exact checked535
theorem derived535 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c535 := by
  apply localUnsat_implies_entails f535 [c530, c300, c533, c6, c24, c31, c90, c534, c204, c60, c230] c535 unsat535 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c300 := h 299 (by decide)
  have h2 : Entails.eval a c533 := derived533 a h
  have h3 : Entails.eval a c6 := h 5 (by decide)
  have h4 : Entails.eval a c24 := h 23 (by decide)
  have h5 : Entails.eval a c31 := h 30 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c534 := derived534 a h
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c60 := h 59 (by decide)
  have h10 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c536 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨21, by decide⟩, true), (⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f536 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c530, some c532, some c300, some c200, some c23, some c93, some c92, some c533, some c240, some c535, some c229, some c248, some c59, some c88, some c204, some c225, some c281, some c325, some c84, some c90, some c495, some c534, some c17, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p536 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked536 : lratChecker f536 p536 = .success := by decide +kernel
theorem unsat536 : Unsatisfiable (PosFin 57) f536 := by
  apply lratCheckerSound f536 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p536
  · intro a ha; simp [p536] at ha; subst a; trivial
  · exact checked536
theorem derived536 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c536 := by
  apply localUnsat_implies_entails f536 [c530, c532, c300, c200, c23, c93, c92, c533, c240, c535, c229, c248, c59, c88, c204, c225, c281, c325, c84, c90, c495, c534, c17] c536 unsat536 (by rfl) a
  have h0 : Entails.eval a c530 := derived530 a h
  have h1 : Entails.eval a c532 := derived532 a h
  have h2 : Entails.eval a c300 := h 299 (by decide)
  have h3 : Entails.eval a c200 := h 199 (by decide)
  have h4 : Entails.eval a c23 := h 22 (by decide)
  have h5 : Entails.eval a c93 := h 92 (by decide)
  have h6 : Entails.eval a c92 := h 91 (by decide)
  have h7 : Entails.eval a c533 := derived533 a h
  have h8 : Entails.eval a c240 := h 239 (by decide)
  have h9 : Entails.eval a c535 := derived535 a h
  have h10 : Entails.eval a c229 := h 228 (by decide)
  have h11 : Entails.eval a c248 := h 247 (by decide)
  have h12 : Entails.eval a c59 := h 58 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c204 := h 203 (by decide)
  have h15 : Entails.eval a c225 := h 224 (by decide)
  have h16 : Entails.eval a c281 := h 280 (by decide)
  have h17 : Entails.eval a c325 := h 324 (by decide)
  have h18 : Entails.eval a c84 := h 83 (by decide)
  have h19 : Entails.eval a c90 := h 89 (by decide)
  have h20 : Entails.eval a c495 := derived495 a h
  have h21 : Entails.eval a c534 := derived534 a h
  have h22 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c537 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f537 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c35, some c8, some c229, some c248, some c146, some c36, some c90, some c3, some c84, some c226, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p537 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked537 : lratChecker f537 p537 = .success := by decide +kernel
theorem unsat537 : Unsatisfiable (PosFin 57) f537 := by
  apply lratCheckerSound f537 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p537
  · intro a ha; simp [p537] at ha; subst a; trivial
  · exact checked537
theorem derived537 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c537 := by
  apply localUnsat_implies_entails f537 [c35, c8, c229, c248, c146, c36, c90, c3, c84, c226] c537 unsat537 (by rfl) a
  have h0 : Entails.eval a c35 := h 34 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c229 := h 228 (by decide)
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c146 := h 145 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c90 := h 89 (by decide)
  have h7 : Entails.eval a c3 := h 2 (by decide)
  have h8 : Entails.eval a c84 := h 83 (by decide)
  have h9 : Entails.eval a c226 := h 225 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c538 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f538 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c93, some c530, some c532, some c300, some c533, some c537, some c536, some c249, some c228, some c58, some c281, some c535, some c229, some c248, some c59, some c88, some c204, some c225, some c316, some c84, some c90, some c534, some c7, some c17, some c145, some c164, some c104, some c102, some c37, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p538 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked538 : lratChecker f538 p538 = .success := by decide +kernel
theorem unsat538 : Unsatisfiable (PosFin 57) f538 := by
  apply lratCheckerSound f538 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p538
  · intro a ha; simp [p538] at ha; subst a; trivial
  · exact checked538
theorem derived538 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c538 := by
  apply localUnsat_implies_entails f538 [c92, c93, c530, c532, c300, c533, c537, c536, c249, c228, c58, c281, c535, c229, c248, c59, c88, c204, c225, c316, c84, c90, c534, c7, c17, c145, c164, c104, c102, c37] c538 unsat538 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c93 := h 92 (by decide)
  have h2 : Entails.eval a c530 := derived530 a h
  have h3 : Entails.eval a c532 := derived532 a h
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c533 := derived533 a h
  have h6 : Entails.eval a c537 := derived537 a h
  have h7 : Entails.eval a c536 := derived536 a h
  have h8 : Entails.eval a c249 := h 248 (by decide)
  have h9 : Entails.eval a c228 := h 227 (by decide)
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c535 := derived535 a h
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c204 := h 203 (by decide)
  have h18 : Entails.eval a c225 := h 224 (by decide)
  have h19 : Entails.eval a c316 := h 315 (by decide)
  have h20 : Entails.eval a c84 := h 83 (by decide)
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c534 := derived534 a h
  have h23 : Entails.eval a c7 := h 6 (by decide)
  have h24 : Entails.eval a c17 := h 16 (by decide)
  have h25 : Entails.eval a c145 := h 144 (by decide)
  have h26 : Entails.eval a c164 := h 163 (by decide)
  have h27 : Entails.eval a c104 := h 103 (by decide)
  have h28 : Entails.eval a c102 := h 101 (by decide)
  have h29 : Entails.eval a c37 := h 36 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c539 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨21, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f539 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c301, some c228, some c281, some c537, some c249, some c533, some c229, some c248, some c59, some c88, some c316, some c84, some c90, some c7, some c25, some c151, some c145, some c17, some c113, some c149, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p539 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked539 : lratChecker f539 p539 = .success := by decide +kernel
theorem unsat539 : Unsatisfiable (PosFin 57) f539 := by
  apply lratCheckerSound f539 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p539
  · intro a ha; simp [p539] at ha; subst a; trivial
  · exact checked539
theorem derived539 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c539 := by
  apply localUnsat_implies_entails f539 [c293, c301, c228, c281, c537, c249, c533, c229, c248, c59, c88, c316, c84, c90, c7, c25, c151, c145, c17, c113, c149] c539 unsat539 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c228 := h 227 (by decide)
  have h3 : Entails.eval a c281 := h 280 (by decide)
  have h4 : Entails.eval a c537 := derived537 a h
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c533 := derived533 a h
  have h7 : Entails.eval a c229 := h 228 (by decide)
  have h8 : Entails.eval a c248 := h 247 (by decide)
  have h9 : Entails.eval a c59 := h 58 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c316 := h 315 (by decide)
  have h12 : Entails.eval a c84 := h 83 (by decide)
  have h13 : Entails.eval a c90 := h 89 (by decide)
  have h14 : Entails.eval a c7 := h 6 (by decide)
  have h15 : Entails.eval a c25 := h 24 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  have h17 : Entails.eval a c145 := h 144 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  have h19 : Entails.eval a c113 := h 112 (by decide)
  have h20 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c540 : DefaultClause 57 := directClause [(⟨21, by decide⟩, false), (⟨35, by decide⟩, false), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨1, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f540 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c537, some c293, some c301, some c533, some c249, some c228, some c58, some c539, some c6, some c24, some c31, some c90, some c534, some c60, some c25, some c230, some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p540 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked540 : lratChecker f540 p540 = .success := by decide +kernel
theorem unsat540 : Unsatisfiable (PosFin 57) f540 := by
  apply lratCheckerSound f540 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p540
  · intro a ha; simp [p540] at ha; subst a; trivial
  · exact checked540
theorem derived540 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c540 := by
  apply localUnsat_implies_entails f540 [c537, c293, c301, c533, c249, c228, c58, c539, c6, c24, c31, c90, c534, c60, c25, c230] c540 unsat540 (by rfl) a
  have h0 : Entails.eval a c537 := derived537 a h
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c301 := h 300 (by decide)
  have h3 : Entails.eval a c533 := derived533 a h
  have h4 : Entails.eval a c249 := h 248 (by decide)
  have h5 : Entails.eval a c228 := h 227 (by decide)
  have h6 : Entails.eval a c58 := h 57 (by decide)
  have h7 : Entails.eval a c539 := derived539 a h
  have h8 : Entails.eval a c6 := h 5 (by decide)
  have h9 : Entails.eval a c24 := h 23 (by decide)
  have h10 : Entails.eval a c31 := h 30 (by decide)
  have h11 : Entails.eval a c90 := h 89 (by decide)
  have h12 : Entails.eval a c534 := derived534 a h
  have h13 : Entails.eval a c60 := h 59 (by decide)
  have h14 : Entails.eval a c25 := h 24 (by decide)
  have h15 : Entails.eval a c230 := h 229 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c541 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨5, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f541 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c6, some c24, some c148, some c105, some c262, some c49, some c196, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p541 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked541 : lratChecker f541 p541 = .success := by decide +kernel
theorem unsat541 : Unsatisfiable (PosFin 57) f541 := by
  apply lratCheckerSound f541 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p541
  · intro a ha; simp [p541] at ha; subst a; trivial
  · exact checked541
theorem derived541 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c541 := by
  apply localUnsat_implies_entails f541 [c6, c24, c148, c105, c262, c49, c196] c541 unsat541 (by rfl) a
  have h0 : Entails.eval a c6 := h 5 (by decide)
  have h1 : Entails.eval a c24 := h 23 (by decide)
  have h2 : Entails.eval a c148 := h 147 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c262 := h 261 (by decide)
  have h5 : Entails.eval a c49 := h 48 (by decide)
  have h6 : Entails.eval a c196 := h 195 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c542 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f542 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c92, some c538, some c293, some c301, some c533, some c537, some c540, some c23, some c200, some c240, some c541, some c229, some c248, some c59, some c88, some c206, some c225, some c281, some c325, some c84, some c90, some c495, some c534, some c17, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p542 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]]
theorem checked542 : lratChecker f542 p542 = .success := by decide +kernel
theorem unsat542 : Unsatisfiable (PosFin 57) f542 := by
  apply lratCheckerSound f542 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p542
  · intro a ha; simp [p542] at ha; subst a; trivial
  · exact checked542
theorem derived542 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c542 := by
  apply localUnsat_implies_entails f542 [c93, c92, c538, c293, c301, c533, c537, c540, c23, c200, c240, c541, c229, c248, c59, c88, c206, c225, c281, c325, c84, c90, c495, c534, c17] c542 unsat542 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c538 := derived538 a h
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c533 := derived533 a h
  have h6 : Entails.eval a c537 := derived537 a h
  have h7 : Entails.eval a c540 := derived540 a h
  have h8 : Entails.eval a c23 := h 22 (by decide)
  have h9 : Entails.eval a c200 := h 199 (by decide)
  have h10 : Entails.eval a c240 := h 239 (by decide)
  have h11 : Entails.eval a c541 := derived541 a h
  have h12 : Entails.eval a c229 := h 228 (by decide)
  have h13 : Entails.eval a c248 := h 247 (by decide)
  have h14 : Entails.eval a c59 := h 58 (by decide)
  have h15 : Entails.eval a c88 := h 87 (by decide)
  have h16 : Entails.eval a c206 := h 205 (by decide)
  have h17 : Entails.eval a c225 := h 224 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c325 := h 324 (by decide)
  have h20 : Entails.eval a c84 := h 83 (by decide)
  have h21 : Entails.eval a c90 := h 89 (by decide)
  have h22 : Entails.eval a c495 := derived495 a h
  have h23 : Entails.eval a c534 := derived534 a h
  have h24 : Entails.eval a c17 := h 16 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c543 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨56, by decide⟩, false), (⟨38, by decide⟩, false), (⟨21, by decide⟩, true), (⟨20, by decide⟩, true), (⟨36, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f543 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c92, some c301, some c23, some c541, some c293, some c200, some c93, some c17, some c149, some c105, some c262, some c38, some c49, some c124, some c106, some c211, some c176, some c120, some c281, some c164, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p543 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked543 : lratChecker f543 p543 = .success := by decide +kernel
theorem unsat543 : Unsatisfiable (PosFin 57) f543 := by
  apply lratCheckerSound f543 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p543
  · intro a ha; simp [p543] at ha; subst a; trivial
  · exact checked543
theorem derived543 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c543 := by
  apply localUnsat_implies_entails f543 [c92, c301, c23, c541, c293, c200, c93, c17, c149, c105, c262, c38, c49, c124, c106, c211, c176, c120, c281, c164] c543 unsat543 (by rfl) a
  have h0 : Entails.eval a c92 := h 91 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c541 := derived541 a h
  have h4 : Entails.eval a c293 := h 292 (by decide)
  have h5 : Entails.eval a c200 := h 199 (by decide)
  have h6 : Entails.eval a c93 := h 92 (by decide)
  have h7 : Entails.eval a c17 := h 16 (by decide)
  have h8 : Entails.eval a c149 := h 148 (by decide)
  have h9 : Entails.eval a c105 := h 104 (by decide)
  have h10 : Entails.eval a c262 := h 261 (by decide)
  have h11 : Entails.eval a c38 := h 37 (by decide)
  have h12 : Entails.eval a c49 := h 48 (by decide)
  have h13 : Entails.eval a c124 := h 123 (by decide)
  have h14 : Entails.eval a c106 := h 105 (by decide)
  have h15 : Entails.eval a c211 := h 210 (by decide)
  have h16 : Entails.eval a c176 := h 175 (by decide)
  have h17 : Entails.eval a c120 := h 119 (by decide)
  have h18 : Entails.eval a c281 := h 280 (by decide)
  have h19 : Entails.eval a c164 := h 163 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c544 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f544 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c93, some c92, some c538, some c293, some c301, some c533, some c23, some c541, some c229, some c248, some c59, some c88, some c206, some c543, some c148, some c151, some c115, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p544 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked544 : lratChecker f544 p544 = .success := by decide +kernel
theorem unsat544 : Unsatisfiable (PosFin 57) f544 := by
  apply lratCheckerSound f544 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p544
  · intro a ha; simp [p544] at ha; subst a; trivial
  · exact checked544
theorem derived544 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c544 := by
  apply localUnsat_implies_entails f544 [c93, c92, c538, c293, c301, c533, c23, c541, c229, c248, c59, c88, c206, c543, c148, c151, c115] c544 unsat544 (by rfl) a
  have h0 : Entails.eval a c93 := h 92 (by decide)
  have h1 : Entails.eval a c92 := h 91 (by decide)
  have h2 : Entails.eval a c538 := derived538 a h
  have h3 : Entails.eval a c293 := h 292 (by decide)
  have h4 : Entails.eval a c301 := h 300 (by decide)
  have h5 : Entails.eval a c533 := derived533 a h
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c541 := derived541 a h
  have h8 : Entails.eval a c229 := h 228 (by decide)
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c59 := h 58 (by decide)
  have h11 : Entails.eval a c88 := h 87 (by decide)
  have h12 : Entails.eval a c206 := h 205 (by decide)
  have h13 : Entails.eval a c543 := derived543 a h
  have h14 : Entails.eval a c148 := h 147 (by decide)
  have h15 : Entails.eval a c151 := h 150 (by decide)
  have h16 : Entails.eval a c115 := h 114 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c545 : DefaultClause 57 := directClause [(⟨22, by decide⟩, false), (⟨40, by decide⟩, false), (⟨1, by decide⟩, false), (⟨4, by decide⟩, false), (⟨18, by decide⟩, false), (⟨50, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f545 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c542, some c544, some c244, some c21, some c90, some c538, some c293, some c301, some c228, some c281, some c93, some c92, some c533, some c229, some c248, some c59, some c88, some c25, some c36, some c7, some c225, some c151, some c17, some c149, some c164, some c105, some c102, some c38, some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨50, by decide⟩, true))]
def p545 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked545 : lratChecker f545 p545 = .success := by decide +kernel
theorem unsat545 : Unsatisfiable (PosFin 57) f545 := by
  apply lratCheckerSound f545 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p545
  · intro a ha; simp [p545] at ha; subst a; trivial
  · exact checked545
theorem derived545 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c545 := by
  apply localUnsat_implies_entails f545 [c542, c544, c244, c21, c90, c538, c293, c301, c228, c281, c93, c92, c533, c229, c248, c59, c88, c25, c36, c7, c225, c151, c17, c149, c164, c105, c102, c38] c545 unsat545 (by rfl) a
  have h0 : Entails.eval a c542 := derived542 a h
  have h1 : Entails.eval a c544 := derived544 a h
  have h2 : Entails.eval a c244 := h 243 (by decide)
  have h3 : Entails.eval a c21 := h 20 (by decide)
  have h4 : Entails.eval a c90 := h 89 (by decide)
  have h5 : Entails.eval a c538 := derived538 a h
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c228 := h 227 (by decide)
  have h9 : Entails.eval a c281 := h 280 (by decide)
  have h10 : Entails.eval a c93 := h 92 (by decide)
  have h11 : Entails.eval a c92 := h 91 (by decide)
  have h12 : Entails.eval a c533 := derived533 a h
  have h13 : Entails.eval a c229 := h 228 (by decide)
  have h14 : Entails.eval a c248 := h 247 (by decide)
  have h15 : Entails.eval a c59 := h 58 (by decide)
  have h16 : Entails.eval a c88 := h 87 (by decide)
  have h17 : Entails.eval a c25 := h 24 (by decide)
  have h18 : Entails.eval a c36 := h 35 (by decide)
  have h19 : Entails.eval a c7 := h 6 (by decide)
  have h20 : Entails.eval a c225 := h 224 (by decide)
  have h21 : Entails.eval a c151 := h 150 (by decide)
  have h22 : Entails.eval a c17 := h 16 (by decide)
  have h23 : Entails.eval a c149 := h 148 (by decide)
  have h24 : Entails.eval a c164 := h 163 (by decide)
  have h25 : Entails.eval a c105 := h 104 (by decide)
  have h26 : Entails.eval a c102 := h 101 (by decide)
  have h27 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c546 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨25, by decide⟩, true), (⟨11, by decide⟩, false), (⟨24, by decide⟩, false), (⟨7, by decide⟩, true), (⟨49, by decide⟩, false), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f546 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c225, some c102, some c164, some c178, some c18, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨25, by decide⟩, false)), some (DefaultClause.unit (⟨11, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p546 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked546 : lratChecker f546 p546 = .success := by decide +kernel
theorem unsat546 : Unsatisfiable (PosFin 57) f546 := by
  apply lratCheckerSound f546 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p546
  · intro a ha; simp [p546] at ha; subst a; trivial
  · exact checked546
theorem derived546 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c546 := by
  apply localUnsat_implies_entails f546 [c225, c102, c164, c178, c18] c546 unsat546 (by rfl) a
  have h0 : Entails.eval a c225 := h 224 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c164 := h 163 (by decide)
  have h3 : Entails.eval a c178 := h 177 (by decide)
  have h4 : Entails.eval a c18 := h 17 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c547 : DefaultClause 57 := directClause [(⟨2, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f547 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c55, some c20, some c511, some c529, some c93, some c92, some c64, some c538, some c293, some c301, some c533, some c542, some c544, some c244, some c228, some c21, some c281, some c90, some c545, some c35, some c6, some c24, some c148, some c105, some c113, some c38, some c546, some c88, some c89, some c324, some (DefaultClause.unit (⟨2, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p547 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]]
theorem checked547 : lratChecker f547 p547 = .success := by decide +kernel
theorem unsat547 : Unsatisfiable (PosFin 57) f547 := by
  apply lratCheckerSound f547 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p547
  · intro a ha; simp [p547] at ha; subst a; trivial
  · exact checked547
theorem derived547 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c547 := by
  apply localUnsat_implies_entails f547 [c55, c20, c511, c529, c93, c92, c64, c538, c293, c301, c533, c542, c544, c244, c228, c21, c281, c90, c545, c35, c6, c24, c148, c105, c113, c38, c546, c88, c89, c324] c547 unsat547 (by rfl) a
  have h0 : Entails.eval a c55 := h 54 (by decide)
  have h1 : Entails.eval a c20 := h 19 (by decide)
  have h2 : Entails.eval a c511 := derived511 a h
  have h3 : Entails.eval a c529 := derived529 a h
  have h4 : Entails.eval a c93 := h 92 (by decide)
  have h5 : Entails.eval a c92 := h 91 (by decide)
  have h6 : Entails.eval a c64 := h 63 (by decide)
  have h7 : Entails.eval a c538 := derived538 a h
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c301 := h 300 (by decide)
  have h10 : Entails.eval a c533 := derived533 a h
  have h11 : Entails.eval a c542 := derived542 a h
  have h12 : Entails.eval a c544 := derived544 a h
  have h13 : Entails.eval a c244 := h 243 (by decide)
  have h14 : Entails.eval a c228 := h 227 (by decide)
  have h15 : Entails.eval a c21 := h 20 (by decide)
  have h16 : Entails.eval a c281 := h 280 (by decide)
  have h17 : Entails.eval a c90 := h 89 (by decide)
  have h18 : Entails.eval a c545 := derived545 a h
  have h19 : Entails.eval a c35 := h 34 (by decide)
  have h20 : Entails.eval a c6 := h 5 (by decide)
  have h21 : Entails.eval a c24 := h 23 (by decide)
  have h22 : Entails.eval a c148 := h 147 (by decide)
  have h23 : Entails.eval a c105 := h 104 (by decide)
  have h24 : Entails.eval a c113 := h 112 (by decide)
  have h25 : Entails.eval a c38 := h 37 (by decide)
  have h26 : Entails.eval a c546 := derived546 a h
  have h27 : Entails.eval a c88 := h 87 (by decide)
  have h28 : Entails.eval a c89 := h 88 (by decide)
  have h29 : Entails.eval a c324 := h 323 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c548 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨19, by decide⟩, true), (⟨20, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f548 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c61, some c89, some c324, some c319, some c280, some c291, some c293, some c202, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p548 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked548 : lratChecker f548 p548 = .success := by decide +kernel
theorem unsat548 : Unsatisfiable (PosFin 57) f548 := by
  apply lratCheckerSound f548 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p548
  · intro a ha; simp [p548] at ha; subst a; trivial
  · exact checked548
theorem derived548 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c548 := by
  apply localUnsat_implies_entails f548 [c61, c89, c324, c319, c280, c291, c293, c202] c548 unsat548 (by rfl) a
  have h0 : Entails.eval a c61 := h 60 (by decide)
  have h1 : Entails.eval a c89 := h 88 (by decide)
  have h2 : Entails.eval a c324 := h 323 (by decide)
  have h3 : Entails.eval a c319 := h 318 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c293 := h 292 (by decide)
  have h7 : Entails.eval a c202 := h 201 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c549 : DefaultClause 57 := directClause [(⟨54, by decide⟩, false), (⟨7, by decide⟩, true), (⟨24, by decide⟩, false), (⟨21, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f549 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c249, some c250, some c547, some c97, some c548, some c237, some c394, some c87, some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨21, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p549 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked549 : lratChecker f549 p549 = .success := by decide +kernel
theorem unsat549 : Unsatisfiable (PosFin 57) f549 := by
  apply lratCheckerSound f549 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p549
  · intro a ha; simp [p549] at ha; subst a; trivial
  · exact checked549
theorem derived549 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c549 := by
  apply localUnsat_implies_entails f549 [c249, c250, c547, c97, c548, c237, c394, c87] c549 unsat549 (by rfl) a
  have h0 : Entails.eval a c249 := h 248 (by decide)
  have h1 : Entails.eval a c250 := h 249 (by decide)
  have h2 : Entails.eval a c547 := derived547 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c548 := derived548 a h
  have h5 : Entails.eval a c237 := h 236 (by decide)
  have h6 : Entails.eval a c394 := derived394 a h
  have h7 : Entails.eval a c87 := h 86 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c550 : DefaultClause 57 := directClause [(⟨22, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f550 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c97, some c98, some c33, some c35, some c249, some c31, some c90, some c549, some c86, some c88, some c237, some (DefaultClause.unit (⟨22, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p550 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked550 : lratChecker f550 p550 = .success := by decide +kernel
theorem unsat550 : Unsatisfiable (PosFin 57) f550 := by
  apply lratCheckerSound f550 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p550
  · intro a ha; simp [p550] at ha; subst a; trivial
  · exact checked550
theorem derived550 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c550 := by
  apply localUnsat_implies_entails f550 [c547, c97, c98, c33, c35, c249, c31, c90, c549, c86, c88, c237] c550 unsat550 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c33 := h 32 (by decide)
  have h4 : Entails.eval a c35 := h 34 (by decide)
  have h5 : Entails.eval a c249 := h 248 (by decide)
  have h6 : Entails.eval a c31 := h 30 (by decide)
  have h7 : Entails.eval a c90 := h 89 (by decide)
  have h8 : Entails.eval a c549 := derived549 a h
  have h9 : Entails.eval a c86 := h 85 (by decide)
  have h10 : Entails.eval a c88 := h 87 (by decide)
  have h11 : Entails.eval a c237 := h 236 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c551 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨7, by decide⟩, true), (⟨56, by decide⟩, false), (⟨53, by decide⟩, false), (⟨38, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f551 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c326, some c325, some c23, some c34, some c498, some c496, some c71, some c294, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p551 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked551 : lratChecker f551 p551 = .success := by decide +kernel
theorem unsat551 : Unsatisfiable (PosFin 57) f551 := by
  apply lratCheckerSound f551 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p551
  · intro a ha; simp [p551] at ha; subst a; trivial
  · exact checked551
theorem derived551 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c551 := by
  apply localUnsat_implies_entails f551 [c326, c325, c23, c34, c498, c496, c71, c294] c551 unsat551 (by rfl) a
  have h0 : Entails.eval a c326 := h 325 (by decide)
  have h1 : Entails.eval a c325 := h 324 (by decide)
  have h2 : Entails.eval a c23 := h 22 (by decide)
  have h3 : Entails.eval a c34 := h 33 (by decide)
  have h4 : Entails.eval a c498 := derived498 a h
  have h5 : Entails.eval a c496 := derived496 a h
  have h6 : Entails.eval a c71 := h 70 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c552 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f552 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c550, some c547, some c97, some c98, some c59, some c86, some c88, some c325, some c326, some c84, some c90, some c551, some c237, some c26, some c36, some c498, some c248, some c243, some c69, some c199, some c294, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p552 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked552 : lratChecker f552 p552 = .success := by decide +kernel
theorem unsat552 : Unsatisfiable (PosFin 57) f552 := by
  apply lratCheckerSound f552 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p552
  · intro a ha; simp [p552] at ha; subst a; trivial
  · exact checked552
theorem derived552 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c552 := by
  apply localUnsat_implies_entails f552 [c550, c547, c97, c98, c59, c86, c88, c325, c326, c84, c90, c551, c237, c26, c36, c498, c248, c243, c69, c199, c294] c552 unsat552 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c59 := h 58 (by decide)
  have h5 : Entails.eval a c86 := h 85 (by decide)
  have h6 : Entails.eval a c88 := h 87 (by decide)
  have h7 : Entails.eval a c325 := h 324 (by decide)
  have h8 : Entails.eval a c326 := h 325 (by decide)
  have h9 : Entails.eval a c84 := h 83 (by decide)
  have h10 : Entails.eval a c90 := h 89 (by decide)
  have h11 : Entails.eval a c551 := derived551 a h
  have h12 : Entails.eval a c237 := h 236 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c36 := h 35 (by decide)
  have h15 : Entails.eval a c498 := derived498 a h
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c243 := h 242 (by decide)
  have h18 : Entails.eval a c69 := h 68 (by decide)
  have h19 : Entails.eval a c199 := h 198 (by decide)
  have h20 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c553 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨52, by decide⟩, true), (⟨51, by decide⟩, true), (⟨39, by decide⟩, false), (⟨7, by decide⟩, true), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f553 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c36, some c498, some c248, some c243, some c68, some c199, some c294, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨52, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p553 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked553 : lratChecker f553 p553 = .success := by decide +kernel
theorem unsat553 : Unsatisfiable (PosFin 57) f553 := by
  apply lratCheckerSound f553 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p553
  · intro a ha; simp [p553] at ha; subst a; trivial
  · exact checked553
theorem derived553 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c553 := by
  apply localUnsat_implies_entails f553 [c26, c36, c498, c248, c243, c68, c199, c294] c553 unsat553 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c36 := h 35 (by decide)
  have h2 : Entails.eval a c498 := derived498 a h
  have h3 : Entails.eval a c248 := h 247 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c68 := h 67 (by decide)
  have h6 : Entails.eval a c199 := h 198 (by decide)
  have h7 : Entails.eval a c294 := h 293 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c554 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨55, by decide⟩, true), (⟨56, by decide⟩, false), (⟨22, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f554 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c60, some c87, some c325, some c326, some c553, some c237, some c23, some c551, some c498, some c70, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p554 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked554 : lratChecker f554 p554 = .success := by decide +kernel
theorem unsat554 : Unsatisfiable (PosFin 57) f554 := by
  apply lratCheckerSound f554 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p554
  · intro a ha; simp [p554] at ha; subst a; trivial
  · exact checked554
theorem derived554 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c554 := by
  apply localUnsat_implies_entails f554 [c60, c87, c325, c326, c553, c237, c23, c551, c498, c70] c554 unsat554 (by rfl) a
  have h0 : Entails.eval a c60 := h 59 (by decide)
  have h1 : Entails.eval a c87 := h 86 (by decide)
  have h2 : Entails.eval a c325 := h 324 (by decide)
  have h3 : Entails.eval a c326 := h 325 (by decide)
  have h4 : Entails.eval a c553 := derived553 a h
  have h5 : Entails.eval a c237 := h 236 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c551 := derived551 a h
  have h8 : Entails.eval a c498 := derived498 a h
  have h9 : Entails.eval a c70 := h 69 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c555 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨17, by decide⟩, true), (⟨14, by decide⟩, false), (⟨38, by decide⟩, false), (⟨35, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f555 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c290, some c151, some c199, some c229, some c248, some c280, some c108, some c162, some c40, some c102, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p555 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked555 : lratChecker f555 p555 = .success := by decide +kernel
theorem unsat555 : Unsatisfiable (PosFin 57) f555 := by
  apply lratCheckerSound f555 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p555
  · intro a ha; simp [p555] at ha; subst a; trivial
  · exact checked555
theorem derived555 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c555 := by
  apply localUnsat_implies_entails f555 [c290, c151, c199, c229, c248, c280, c108, c162, c40, c102] c555 unsat555 (by rfl) a
  have h0 : Entails.eval a c290 := h 289 (by decide)
  have h1 : Entails.eval a c151 := h 150 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  have h3 : Entails.eval a c229 := h 228 (by decide)
  have h4 : Entails.eval a c248 := h 247 (by decide)
  have h5 : Entails.eval a c280 := h 279 (by decide)
  have h6 : Entails.eval a c108 := h 107 (by decide)
  have h7 : Entails.eval a c162 := h 161 (by decide)
  have h8 : Entails.eval a c40 := h 39 (by decide)
  have h9 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c556 : DefaultClause 57 := directClause [(⟨53, by decide⟩, false), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f556 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c98, some c97, some c550, some c552, some c394, some c554, some c96, some c415, some c325, some c326, some c237, some c23, some c5, some c498, some c176, some c144, some c70, some c17, some c3, some c240, some c555, some c285, some c292, some c148, some c199, some c229, some c247, some c280, some c105, some c162, some c38, some c102, some (DefaultClause.unit (⟨53, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p556 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]]
theorem checked556 : lratChecker f556 p556 = .success := by decide +kernel
theorem unsat556 : Unsatisfiable (PosFin 57) f556 := by
  apply lratCheckerSound f556 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p556
  · intro a ha; simp [p556] at ha; subst a; trivial
  · exact checked556
theorem derived556 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c556 := by
  apply localUnsat_implies_entails f556 [c547, c98, c97, c550, c552, c394, c554, c96, c415, c325, c326, c237, c23, c5, c498, c176, c144, c70, c17, c3, c240, c555, c285, c292, c148, c199, c229, c247, c280, c105, c162, c38, c102] c556 unsat556 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c394 := derived394 a h
  have h6 : Entails.eval a c554 := derived554 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c415 := derived415 a h
  have h9 : Entails.eval a c325 := h 324 (by decide)
  have h10 : Entails.eval a c326 := h 325 (by decide)
  have h11 : Entails.eval a c237 := h 236 (by decide)
  have h12 : Entails.eval a c23 := h 22 (by decide)
  have h13 : Entails.eval a c5 := h 4 (by decide)
  have h14 : Entails.eval a c498 := derived498 a h
  have h15 : Entails.eval a c176 := h 175 (by decide)
  have h16 : Entails.eval a c144 := h 143 (by decide)
  have h17 : Entails.eval a c70 := h 69 (by decide)
  have h18 : Entails.eval a c17 := h 16 (by decide)
  have h19 : Entails.eval a c3 := h 2 (by decide)
  have h20 : Entails.eval a c240 := h 239 (by decide)
  have h21 : Entails.eval a c555 := derived555 a h
  have h22 : Entails.eval a c285 := h 284 (by decide)
  have h23 : Entails.eval a c292 := h 291 (by decide)
  have h24 : Entails.eval a c148 := h 147 (by decide)
  have h25 : Entails.eval a c199 := h 198 (by decide)
  have h26 : Entails.eval a c229 := h 228 (by decide)
  have h27 : Entails.eval a c247 := h 246 (by decide)
  have h28 : Entails.eval a c280 := h 279 (by decide)
  have h29 : Entails.eval a c105 := h 104 (by decide)
  have h30 : Entails.eval a c162 := h 161 (by decide)
  have h31 : Entails.eval a c38 := h 37 (by decide)
  have h32 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c557 : DefaultClause 57 := directClause [(⟨13, by decide⟩, false), (⟨17, by decide⟩, true), (⟨36, by decide⟩, false), (⟨49, by decide⟩, false), (⟨20, by decide⟩, true), (⟨37, by decide⟩, false), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨54, by decide⟩, false), (⟨6, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f557 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c144, some c147, some c13, some c105, some c162, some c38, some c102, some (DefaultClause.unit (⟨13, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p557 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked557 : lratChecker f557 p557 = .success := by decide +kernel
theorem unsat557 : Unsatisfiable (PosFin 57) f557 := by
  apply lratCheckerSound f557 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p557
  · intro a ha; simp [p557] at ha; subst a; trivial
  · exact checked557
theorem derived557 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c557 := by
  apply localUnsat_implies_entails f557 [c144, c147, c13, c105, c162, c38, c102] c557 unsat557 (by rfl) a
  have h0 : Entails.eval a c144 := h 143 (by decide)
  have h1 : Entails.eval a c147 := h 146 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c105 := h 104 (by decide)
  have h4 : Entails.eval a c162 := h 161 (by decide)
  have h5 : Entails.eval a c38 := h 37 (by decide)
  have h6 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c558 : DefaultClause 57 := directClause [(⟨18, by decide⟩, false), (⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f558 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c415, some c547, some c97, some c98, some c229, some c248, some c247, some c280, some c204, some c225, some c557, some c15, some c162, some c148, some c102, some c105, some c38, some (DefaultClause.unit (⟨18, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p558 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked558 : lratChecker f558 p558 = .success := by decide +kernel
theorem unsat558 : Unsatisfiable (PosFin 57) f558 := by
  apply lratCheckerSound f558 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p558
  · intro a ha; simp [p558] at ha; subst a; trivial
  · exact checked558
theorem derived558 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c558 := by
  apply localUnsat_implies_entails f558 [c415, c547, c97, c98, c229, c248, c247, c280, c204, c225, c557, c15, c162, c148, c102, c105, c38] c558 unsat558 (by rfl) a
  have h0 : Entails.eval a c415 := derived415 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c229 := h 228 (by decide)
  have h5 : Entails.eval a c248 := h 247 (by decide)
  have h6 : Entails.eval a c247 := h 246 (by decide)
  have h7 : Entails.eval a c280 := h 279 (by decide)
  have h8 : Entails.eval a c204 := h 203 (by decide)
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c557 := derived557 a h
  have h11 : Entails.eval a c15 := h 14 (by decide)
  have h12 : Entails.eval a c162 := h 161 (by decide)
  have h13 : Entails.eval a c148 := h 147 (by decide)
  have h14 : Entails.eval a c102 := h 101 (by decide)
  have h15 : Entails.eval a c105 := h 104 (by decide)
  have h16 : Entails.eval a c38 := h 37 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c559 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨39, by decide⟩, true), (⟨38, by decide⟩, false), (⟨37, by decide⟩, false), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f559 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c415, some c547, some c97, some c98, some c558, some c199, some c242, some c225, some c240, some c243, some c280, some c3, some c204, some c144, some c15, some c148, some c168, some c105, some c103, some c43, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p559 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked559 : lratChecker f559 p559 = .success := by decide +kernel
theorem unsat559 : Unsatisfiable (PosFin 57) f559 := by
  apply lratCheckerSound f559 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p559
  · intro a ha; simp [p559] at ha; subst a; trivial
  · exact checked559
theorem derived559 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c559 := by
  apply localUnsat_implies_entails f559 [c415, c547, c97, c98, c558, c199, c242, c225, c240, c243, c280, c3, c204, c144, c15, c148, c168, c105, c103, c43] c559 unsat559 (by rfl) a
  have h0 : Entails.eval a c415 := derived415 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c558 := derived558 a h
  have h5 : Entails.eval a c199 := h 198 (by decide)
  have h6 : Entails.eval a c242 := h 241 (by decide)
  have h7 : Entails.eval a c225 := h 224 (by decide)
  have h8 : Entails.eval a c240 := h 239 (by decide)
  have h9 : Entails.eval a c243 := h 242 (by decide)
  have h10 : Entails.eval a c280 := h 279 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c204 := h 203 (by decide)
  have h13 : Entails.eval a c144 := h 143 (by decide)
  have h14 : Entails.eval a c15 := h 14 (by decide)
  have h15 : Entails.eval a c148 := h 147 (by decide)
  have h16 : Entails.eval a c168 := h 167 (by decide)
  have h17 : Entails.eval a c105 := h 104 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c43 := h 42 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c560 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨24, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f560 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c98, some c97, some c550, some c552, some c394, some c554, some c96, some c415, some c556, some c58, some c300, some c70, some c559, some c292, some c285, some c379, some c236, some c38, some c43, some c204, some c248, some c243, some c190, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p560 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]]
theorem checked560 : lratChecker f560 p560 = .success := by decide +kernel
theorem unsat560 : Unsatisfiable (PosFin 57) f560 := by
  apply lratCheckerSound f560 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p560
  · intro a ha; simp [p560] at ha; subst a; trivial
  · exact checked560
theorem derived560 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c560 := by
  apply localUnsat_implies_entails f560 [c547, c98, c97, c550, c552, c394, c554, c96, c415, c556, c58, c300, c70, c559, c292, c285, c379, c236, c38, c43, c204, c248, c243, c190] c560 unsat560 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c394 := derived394 a h
  have h6 : Entails.eval a c554 := derived554 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c415 := derived415 a h
  have h9 : Entails.eval a c556 := derived556 a h
  have h10 : Entails.eval a c58 := h 57 (by decide)
  have h11 : Entails.eval a c300 := h 299 (by decide)
  have h12 : Entails.eval a c70 := h 69 (by decide)
  have h13 : Entails.eval a c559 := derived559 a h
  have h14 : Entails.eval a c292 := h 291 (by decide)
  have h15 : Entails.eval a c285 := h 284 (by decide)
  have h16 : Entails.eval a c379 := derived379 a h
  have h17 : Entails.eval a c236 := h 235 (by decide)
  have h18 : Entails.eval a c38 := h 37 (by decide)
  have h19 : Entails.eval a c43 := h 42 (by decide)
  have h20 : Entails.eval a c204 := h 203 (by decide)
  have h21 : Entails.eval a c248 := h 247 (by decide)
  have h22 : Entails.eval a c243 := h 242 (by decide)
  have h23 : Entails.eval a c190 := h 189 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c561 : DefaultClause 57 := directClause [(⟨14, by decide⟩, true), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f561 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c17, some c15, some c13, some c188, some (DefaultClause.unit (⟨14, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p561 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked561 : lratChecker f561 p561 = .success := by decide +kernel
theorem unsat561 : Unsatisfiable (PosFin 57) f561 := by
  apply lratCheckerSound f561 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p561
  · intro a ha; simp [p561] at ha; subst a; trivial
  · exact checked561
theorem derived561 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c561 := by
  apply localUnsat_implies_entails f561 [c17, c15, c13, c188] c561 unsat561 (by rfl) a
  have h0 : Entails.eval a c17 := h 16 (by decide)
  have h1 : Entails.eval a c15 := h 14 (by decide)
  have h2 : Entails.eval a c13 := h 12 (by decide)
  have h3 : Entails.eval a c188 := h 187 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c562 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨17, by decide⟩, true), (⟨39, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f562 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c98, some c97, some c96, some c561, some c552, some c550, some c555, some c70, some c68, some c300, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p562 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked562 : lratChecker f562 p562 = .success := by decide +kernel
theorem unsat562 : Unsatisfiable (PosFin 57) f562 := by
  apply lratCheckerSound f562 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p562
  · intro a ha; simp [p562] at ha; subst a; trivial
  · exact checked562
theorem derived562 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c562 := by
  apply localUnsat_implies_entails f562 [c547, c98, c97, c96, c561, c552, c550, c555, c70, c68, c300] c562 unsat562 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c96 := h 95 (by decide)
  have h4 : Entails.eval a c561 := derived561 a h
  have h5 : Entails.eval a c552 := derived552 a h
  have h6 : Entails.eval a c550 := derived550 a h
  have h7 : Entails.eval a c555 := derived555 a h
  have h8 : Entails.eval a c70 := h 69 (by decide)
  have h9 : Entails.eval a c68 := h 67 (by decide)
  have h10 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c563 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨39, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f563 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c98, some c97, some c550, some c552, some c394, some c554, some c96, some c562, some c56, some c415, some c66, some c316, some c26, some c294, some c280, some c199, some c545, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p563 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked563 : lratChecker f563 p563 = .success := by decide +kernel
theorem unsat563 : Unsatisfiable (PosFin 57) f563 := by
  apply lratCheckerSound f563 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p563
  · intro a ha; simp [p563] at ha; subst a; trivial
  · exact checked563
theorem derived563 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c563 := by
  apply localUnsat_implies_entails f563 [c547, c98, c97, c550, c552, c394, c554, c96, c562, c56, c415, c66, c316, c26, c294, c280, c199, c545] c563 unsat563 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c394 := derived394 a h
  have h6 : Entails.eval a c554 := derived554 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c562 := derived562 a h
  have h9 : Entails.eval a c56 := h 55 (by decide)
  have h10 : Entails.eval a c415 := derived415 a h
  have h11 : Entails.eval a c66 := h 65 (by decide)
  have h12 : Entails.eval a c316 := h 315 (by decide)
  have h13 : Entails.eval a c26 := h 25 (by decide)
  have h14 : Entails.eval a c294 := h 293 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c199 := h 198 (by decide)
  have h17 : Entails.eval a c545 := derived545 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c564 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨39, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f564 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c550, some c552, some c563, some c223, some c243, some c547, some c98, some c97, some c394, some c554, some c96, some c561, some c415, some c66, some c26, some c294, some c151, some c280, some c108, some c545, some c168, some c46, some c103, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p564 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked564 : lratChecker f564 p564 = .success := by decide +kernel
theorem unsat564 : Unsatisfiable (PosFin 57) f564 := by
  apply lratCheckerSound f564 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p564
  · intro a ha; simp [p564] at ha; subst a; trivial
  · exact checked564
theorem derived564 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c564 := by
  apply localUnsat_implies_entails f564 [c550, c552, c563, c223, c243, c547, c98, c97, c394, c554, c96, c561, c415, c66, c26, c294, c151, c280, c108, c545, c168, c46, c103] c564 unsat564 (by rfl) a
  have h0 : Entails.eval a c550 := derived550 a h
  have h1 : Entails.eval a c552 := derived552 a h
  have h2 : Entails.eval a c563 := derived563 a h
  have h3 : Entails.eval a c223 := h 222 (by decide)
  have h4 : Entails.eval a c243 := h 242 (by decide)
  have h5 : Entails.eval a c547 := derived547 a h
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c97 := h 96 (by decide)
  have h8 : Entails.eval a c394 := derived394 a h
  have h9 : Entails.eval a c554 := derived554 a h
  have h10 : Entails.eval a c96 := h 95 (by decide)
  have h11 : Entails.eval a c561 := derived561 a h
  have h12 : Entails.eval a c415 := derived415 a h
  have h13 : Entails.eval a c66 := h 65 (by decide)
  have h14 : Entails.eval a c26 := h 25 (by decide)
  have h15 : Entails.eval a c294 := h 293 (by decide)
  have h16 : Entails.eval a c151 := h 150 (by decide)
  have h17 : Entails.eval a c280 := h 279 (by decide)
  have h18 : Entails.eval a c108 := h 107 (by decide)
  have h19 : Entails.eval a c545 := derived545 a h
  have h20 : Entails.eval a c168 := h 167 (by decide)
  have h21 : Entails.eval a c46 := h 45 (by decide)
  have h22 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c565 : DefaultClause 57 := directClause [(⟨39, by decide⟩, false), (⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f565 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c98, some c97, some c550, some c552, some c394, some c554, some c96, some c561, some c563, some c241, some c243, some c223, some c564, some c290, some c280, some c229, some c168, some c103, some c46, some c43, some c195, some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p565 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked565 : lratChecker f565 p565 = .success := by decide +kernel
theorem unsat565 : Unsatisfiable (PosFin 57) f565 := by
  apply lratCheckerSound f565 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p565
  · intro a ha; simp [p565] at ha; subst a; trivial
  · exact checked565
theorem derived565 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c565 := by
  apply localUnsat_implies_entails f565 [c547, c98, c97, c550, c552, c394, c554, c96, c561, c563, c241, c243, c223, c564, c290, c280, c229, c168, c103, c46, c43, c195] c565 unsat565 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c394 := derived394 a h
  have h6 : Entails.eval a c554 := derived554 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c561 := derived561 a h
  have h9 : Entails.eval a c563 := derived563 a h
  have h10 : Entails.eval a c241 := h 240 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c223 := h 222 (by decide)
  have h13 : Entails.eval a c564 := derived564 a h
  have h14 : Entails.eval a c290 := h 289 (by decide)
  have h15 : Entails.eval a c280 := h 279 (by decide)
  have h16 : Entails.eval a c229 := h 228 (by decide)
  have h17 : Entails.eval a c168 := h 167 (by decide)
  have h18 : Entails.eval a c103 := h 102 (by decide)
  have h19 : Entails.eval a c46 := h 45 (by decide)
  have h20 : Entails.eval a c43 := h 42 (by decide)
  have h21 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c566 : DefaultClause 57 := directClause [(⟨35, by decide⟩, false), (⟨16, by decide⟩, false), (⟨40, by decide⟩, false), (⟨39, by decide⟩, true), (⟨14, by decide⟩, false), (⟨3, by decide⟩, true), (⟨56, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f566 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c394, some c547, some c97, some c98, some c300, some c291, some c146, some c23, some c68, some c58, some c3, some c244, some c326, some c199, some c285, some c241, some c223, some c148, some c280, some c105, some c168, some c43, some c103, some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p566 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]]
theorem checked566 : lratChecker f566 p566 = .success := by decide +kernel
theorem unsat566 : Unsatisfiable (PosFin 57) f566 := by
  apply lratCheckerSound f566 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p566
  · intro a ha; simp [p566] at ha; subst a; trivial
  · exact checked566
theorem derived566 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c566 := by
  apply localUnsat_implies_entails f566 [c394, c547, c97, c98, c300, c291, c146, c23, c68, c58, c3, c244, c326, c199, c285, c241, c223, c148, c280, c105, c168, c43, c103] c566 unsat566 (by rfl) a
  have h0 : Entails.eval a c394 := derived394 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c291 := h 290 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c23 := h 22 (by decide)
  have h8 : Entails.eval a c68 := h 67 (by decide)
  have h9 : Entails.eval a c58 := h 57 (by decide)
  have h10 : Entails.eval a c3 := h 2 (by decide)
  have h11 : Entails.eval a c244 := h 243 (by decide)
  have h12 : Entails.eval a c326 := h 325 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  have h14 : Entails.eval a c285 := h 284 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c223 := h 222 (by decide)
  have h17 : Entails.eval a c148 := h 147 (by decide)
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c105 := h 104 (by decide)
  have h20 : Entails.eval a c168 := h 167 (by decide)
  have h21 : Entails.eval a c43 := h 42 (by decide)
  have h22 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c567 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f567 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c552, some c550, some c547, some c97, some c98, some c394, some c554, some c96, some c561, some c565, some c560, some c26, some c8, some c566, some c56, some c66, some c325, some c316, some c58, some c301, some c285, some c323, some c235, some c174, some c280, some c204, some c105, some c136, some c243, some c38, some c102, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p567 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]]
theorem checked567 : lratChecker f567 p567 = .success := by decide +kernel
theorem unsat567 : Unsatisfiable (PosFin 57) f567 := by
  apply lratCheckerSound f567 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p567
  · intro a ha; simp [p567] at ha; subst a; trivial
  · exact checked567
theorem derived567 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c567 := by
  apply localUnsat_implies_entails f567 [c552, c550, c547, c97, c98, c394, c554, c96, c561, c565, c560, c26, c8, c566, c56, c66, c325, c316, c58, c301, c285, c323, c235, c174, c280, c204, c105, c136, c243, c38, c102] c567 unsat567 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c550 := derived550 a h
  have h2 : Entails.eval a c547 := derived547 a h
  have h3 : Entails.eval a c97 := h 96 (by decide)
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c394 := derived394 a h
  have h6 : Entails.eval a c554 := derived554 a h
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c561 := derived561 a h
  have h9 : Entails.eval a c565 := derived565 a h
  have h10 : Entails.eval a c560 := derived560 a h
  have h11 : Entails.eval a c26 := h 25 (by decide)
  have h12 : Entails.eval a c8 := h 7 (by decide)
  have h13 : Entails.eval a c566 := derived566 a h
  have h14 : Entails.eval a c56 := h 55 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c325 := h 324 (by decide)
  have h17 : Entails.eval a c316 := h 315 (by decide)
  have h18 : Entails.eval a c58 := h 57 (by decide)
  have h19 : Entails.eval a c301 := h 300 (by decide)
  have h20 : Entails.eval a c285 := h 284 (by decide)
  have h21 : Entails.eval a c323 := h 322 (by decide)
  have h22 : Entails.eval a c235 := h 234 (by decide)
  have h23 : Entails.eval a c174 := h 173 (by decide)
  have h24 : Entails.eval a c280 := h 279 (by decide)
  have h25 : Entails.eval a c204 := h 203 (by decide)
  have h26 : Entails.eval a c105 := h 104 (by decide)
  have h27 : Entails.eval a c136 := h 135 (by decide)
  have h28 : Entails.eval a c243 := h 242 (by decide)
  have h29 : Entails.eval a c38 := h 37 (by decide)
  have h30 : Entails.eval a c102 := h 101 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c568 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨28, by decide⟩, true), (⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨36, by decide⟩, true), (⟨14, by decide⟩, false), (⟨39, by decide⟩, true), (⟨22, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f568 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c204, some c105, some c248, some c186, some c110, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨28, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true))]
def p568 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked568 : lratChecker f568 p568 = .success := by decide +kernel
theorem unsat568 : Unsatisfiable (PosFin 57) f568 := by
  apply lratCheckerSound f568 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p568
  · intro a ha; simp [p568] at ha; subst a; trivial
  · exact checked568
theorem derived568 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c568 := by
  apply localUnsat_implies_entails f568 [c204, c105, c248, c186, c110] c568 unsat568 (by rfl) a
  have h0 : Entails.eval a c204 := h 203 (by decide)
  have h1 : Entails.eval a c105 := h 104 (by decide)
  have h2 : Entails.eval a c248 := h 247 (by decide)
  have h3 : Entails.eval a c186 := h 185 (by decide)
  have h4 : Entails.eval a c110 := h 109 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c569 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨9, by decide⟩, true), (⟨36, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f569 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c102, some c38, some c40, some c568, some c247, some c110, some c186, some c187, some c131, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p569 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked569 : lratChecker f569 p569 = .success := by decide +kernel
theorem unsat569 : Unsatisfiable (PosFin 57) f569 := by
  apply lratCheckerSound f569 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p569
  · intro a ha; simp [p569] at ha; subst a; trivial
  · exact checked569
theorem derived569 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c569 := by
  apply localUnsat_implies_entails f569 [c102, c38, c40, c568, c247, c110, c186, c187, c131] c569 unsat569 (by rfl) a
  have h0 : Entails.eval a c102 := h 101 (by decide)
  have h1 : Entails.eval a c38 := h 37 (by decide)
  have h2 : Entails.eval a c40 := h 39 (by decide)
  have h3 : Entails.eval a c568 := derived568 a h
  have h4 : Entails.eval a c247 := h 246 (by decide)
  have h5 : Entails.eval a c110 := h 109 (by decide)
  have h6 : Entails.eval a c186 := h 185 (by decide)
  have h7 : Entails.eval a c187 := h 186 (by decide)
  have h8 : Entails.eval a c131 := h 130 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c570 : DefaultClause 57 := directClause [(⟨9, by decide⟩, true), (⟨36, by decide⟩, true), (⟨1, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, true), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f570 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c569, some c241, some c243, some c204, some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true))]
def p570 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked570 : lratChecker f570 p570 = .success := by decide +kernel
theorem unsat570 : Unsatisfiable (PosFin 57) f570 := by
  apply lratCheckerSound f570 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p570
  · intro a ha; simp [p570] at ha; subst a; trivial
  · exact checked570
theorem derived570 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c570 := by
  apply localUnsat_implies_entails f570 [c569, c241, c243, c204] c570 unsat570 (by rfl) a
  have h0 : Entails.eval a c569 := derived569 a h
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c243 := h 242 (by decide)
  have h3 : Entails.eval a c204 := h 203 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c571 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨38, by decide⟩, false), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f571 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c136, some c570, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨38, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true))]
def p571 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked571 : lratChecker f571 p571 = .success := by decide +kernel
theorem unsat571 : Unsatisfiable (PosFin 57) f571 := by
  apply lratCheckerSound f571 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p571
  · intro a ha; simp [p571] at ha; subst a; trivial
  · exact checked571
theorem derived571 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c571 := by
  apply localUnsat_implies_entails f571 [c293, c136, c570] c571 unsat571 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c136 := h 135 (by decide)
  have h2 : Entails.eval a c570 := derived570 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c572 : DefaultClause 57 := directClause [(⟨36, by decide⟩, true), (⟨55, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, true), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f572 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c570, some c285, some c162, some c323, some c280, some (DefaultClause.unit (⟨36, by decide⟩, false)), some (DefaultClause.unit (⟨55, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p572 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked572 : lratChecker f572 p572 = .success := by decide +kernel
theorem unsat572 : Unsatisfiable (PosFin 57) f572 := by
  apply lratCheckerSound f572 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p572
  · intro a ha; simp [p572] at ha; subst a; trivial
  · exact checked572
theorem derived572 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c572 := by
  apply localUnsat_implies_entails f572 [c570, c285, c162, c323, c280] c572 unsat572 (by rfl) a
  have h0 : Entails.eval a c570 := derived570 a h
  have h1 : Entails.eval a c285 := h 284 (by decide)
  have h2 : Entails.eval a c162 := h 161 (by decide)
  have h3 : Entails.eval a c323 := h 322 (by decide)
  have h4 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c573 : DefaultClause 57 := directClause [(⟨35, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨39, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f573 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c96, some c97, some c98, some c21, some c56, some c66, some c571, some c480, some c572, some c301, some c23, some c58, some c231, some (DefaultClause.unit (⟨35, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p573 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked573 : lratChecker f573 p573 = .success := by decide +kernel
theorem unsat573 : Unsatisfiable (PosFin 57) f573 := by
  apply lratCheckerSound f573 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p573
  · intro a ha; simp [p573] at ha; subst a; trivial
  · exact checked573
theorem derived573 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c573 := by
  apply localUnsat_implies_entails f573 [c547, c96, c97, c98, c21, c56, c66, c571, c480, c572, c301, c23, c58, c231] c573 unsat573 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c56 := h 55 (by decide)
  have h6 : Entails.eval a c66 := h 65 (by decide)
  have h7 : Entails.eval a c571 := derived571 a h
  have h8 : Entails.eval a c480 := derived480 a h
  have h9 : Entails.eval a c572 := derived572 a h
  have h10 : Entails.eval a c301 := h 300 (by decide)
  have h11 : Entails.eval a c23 := h 22 (by decide)
  have h12 : Entails.eval a c58 := h 57 (by decide)
  have h13 : Entails.eval a c231 := h 230 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c574 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨35, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f574 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c97, some c567, some c61, some c300, some c58, some c23, some c291, some c98, some c96, some c561, some c552, some c550, some c231, some c320, some c3, some c280, some c146, some c223, some c162, some c8, some c199, some c102, some c250, some c248, some c38, some c40, some c195, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p574 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]]
theorem checked574 : lratChecker f574 p574 = .success := by decide +kernel
theorem unsat574 : Unsatisfiable (PosFin 57) f574 := by
  apply lratCheckerSound f574 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p574
  · intro a ha; simp [p574] at ha; subst a; trivial
  · exact checked574
theorem derived574 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c574 := by
  apply localUnsat_implies_entails f574 [c547, c97, c567, c61, c300, c58, c23, c291, c98, c96, c561, c552, c550, c231, c320, c3, c280, c146, c223, c162, c8, c199, c102, c250, c248, c38, c40, c195] c574 unsat574 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c567 := derived567 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c300 := h 299 (by decide)
  have h5 : Entails.eval a c58 := h 57 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c98 := h 97 (by decide)
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c561 := derived561 a h
  have h11 : Entails.eval a c552 := derived552 a h
  have h12 : Entails.eval a c550 := derived550 a h
  have h13 : Entails.eval a c231 := h 230 (by decide)
  have h14 : Entails.eval a c320 := h 319 (by decide)
  have h15 : Entails.eval a c3 := h 2 (by decide)
  have h16 : Entails.eval a c280 := h 279 (by decide)
  have h17 : Entails.eval a c146 := h 145 (by decide)
  have h18 : Entails.eval a c223 := h 222 (by decide)
  have h19 : Entails.eval a c162 := h 161 (by decide)
  have h20 : Entails.eval a c8 := h 7 (by decide)
  have h21 : Entails.eval a c199 := h 198 (by decide)
  have h22 : Entails.eval a c102 := h 101 (by decide)
  have h23 : Entails.eval a c250 := h 249 (by decide)
  have h24 : Entails.eval a c248 := h 247 (by decide)
  have h25 : Entails.eval a c38 := h 37 (by decide)
  have h26 : Entails.eval a c40 := h 39 (by decide)
  have h27 : Entails.eval a c195 := h 194 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c575 : DefaultClause 57 := directClause [(⟨16, by decide⟩, true), (⟨36, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, false), (⟨14, by decide⟩, false), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f575 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c97, some c98, some c300, some c68, some c148, some c23, some c291, some c8, some c250, some c105, some c43, some c263, some c128, some c126, some c168, some c277, some c278, some c280, some c304, some c317, some (DefaultClause.unit (⟨16, by decide⟩, false)), some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p575 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]]
theorem checked575 : lratChecker f575 p575 = .success := by decide +kernel
theorem unsat575 : Unsatisfiable (PosFin 57) f575 := by
  apply lratCheckerSound f575 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p575
  · intro a ha; simp [p575] at ha; subst a; trivial
  · exact checked575
theorem derived575 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c575 := by
  apply localUnsat_implies_entails f575 [c547, c97, c98, c300, c68, c148, c23, c291, c8, c250, c105, c43, c263, c128, c126, c168, c277, c278, c280, c304, c317] c575 unsat575 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c148 := h 147 (by decide)
  have h6 : Entails.eval a c23 := h 22 (by decide)
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c8 := h 7 (by decide)
  have h9 : Entails.eval a c250 := h 249 (by decide)
  have h10 : Entails.eval a c105 := h 104 (by decide)
  have h11 : Entails.eval a c43 := h 42 (by decide)
  have h12 : Entails.eval a c263 := h 262 (by decide)
  have h13 : Entails.eval a c128 := h 127 (by decide)
  have h14 : Entails.eval a c126 := h 125 (by decide)
  have h15 : Entails.eval a c168 := h 167 (by decide)
  have h16 : Entails.eval a c277 := h 276 (by decide)
  have h17 : Entails.eval a c278 := h 277 (by decide)
  have h18 : Entails.eval a c280 := h 279 (by decide)
  have h19 : Entails.eval a c304 := h 303 (by decide)
  have h20 : Entails.eval a c317 := h 316 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c576 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨51, by decide⟩, true), (⟨35, by decide⟩, false), (⟨3, by decide⟩, true), (⟨40, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f576 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c97, some c98, some c300, some c68, some c23, some c291, some c561, some c148, some c575, some c146, some c3, some c249, some c244, some c199, some c241, some c105, some c43, some c263, some c192, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨35, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p576 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]]
theorem checked576 : lratChecker f576 p576 = .success := by decide +kernel
theorem unsat576 : Unsatisfiable (PosFin 57) f576 := by
  apply lratCheckerSound f576 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p576
  · intro a ha; simp [p576] at ha; subst a; trivial
  · exact checked576
theorem derived576 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c576 := by
  apply localUnsat_implies_entails f576 [c547, c97, c98, c300, c68, c23, c291, c561, c148, c575, c146, c3, c249, c244, c199, c241, c105, c43, c263, c192] c576 unsat576 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c300 := h 299 (by decide)
  have h4 : Entails.eval a c68 := h 67 (by decide)
  have h5 : Entails.eval a c23 := h 22 (by decide)
  have h6 : Entails.eval a c291 := h 290 (by decide)
  have h7 : Entails.eval a c561 := derived561 a h
  have h8 : Entails.eval a c148 := h 147 (by decide)
  have h9 : Entails.eval a c575 := derived575 a h
  have h10 : Entails.eval a c146 := h 145 (by decide)
  have h11 : Entails.eval a c3 := h 2 (by decide)
  have h12 : Entails.eval a c249 := h 248 (by decide)
  have h13 : Entails.eval a c244 := h 243 (by decide)
  have h14 : Entails.eval a c199 := h 198 (by decide)
  have h15 : Entails.eval a c241 := h 240 (by decide)
  have h16 : Entails.eval a c105 := h 104 (by decide)
  have h17 : Entails.eval a c43 := h 42 (by decide)
  have h18 : Entails.eval a c263 := h 262 (by decide)
  have h19 : Entails.eval a c192 := h 191 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c577 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f577 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c567, some c61, some c552, some c550, some c547, some c97, some c98, some c96, some c561, some c573, some c291, some c574, some c576, some c570, some c572, some c162, some c324, some c280, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p577 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]]
theorem checked577 : lratChecker f577 p577 = .success := by decide +kernel
theorem unsat577 : Unsatisfiable (PosFin 57) f577 := by
  apply lratCheckerSound f577 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p577
  · intro a ha; simp [p577] at ha; subst a; trivial
  · exact checked577
theorem derived577 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c577 := by
  apply localUnsat_implies_entails f577 [c567, c61, c552, c550, c547, c97, c98, c96, c561, c573, c291, c574, c576, c570, c572, c162, c324, c280] c577 unsat577 (by rfl) a
  have h0 : Entails.eval a c567 := derived567 a h
  have h1 : Entails.eval a c61 := h 60 (by decide)
  have h2 : Entails.eval a c552 := derived552 a h
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c97 := h 96 (by decide)
  have h6 : Entails.eval a c98 := h 97 (by decide)
  have h7 : Entails.eval a c96 := h 95 (by decide)
  have h8 : Entails.eval a c561 := derived561 a h
  have h9 : Entails.eval a c573 := derived573 a h
  have h10 : Entails.eval a c291 := h 290 (by decide)
  have h11 : Entails.eval a c574 := derived574 a h
  have h12 : Entails.eval a c576 := derived576 a h
  have h13 : Entails.eval a c570 := derived570 a h
  have h14 : Entails.eval a c572 := derived572 a h
  have h15 : Entails.eval a c162 := h 161 (by decide)
  have h16 : Entails.eval a c324 := h 323 (by decide)
  have h17 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c578 : DefaultClause 57 := directClause [(⟨39, by decide⟩, true), (⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f578 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c552, some c550, some c577, some c60, some c25, some c238, some (DefaultClause.unit (⟨39, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p578 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked578 : lratChecker f578 p578 = .success := by decide +kernel
theorem unsat578 : Unsatisfiable (PosFin 57) f578 := by
  apply lratCheckerSound f578 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p578
  · intro a ha; simp [p578] at ha; subst a; trivial
  · exact checked578
theorem derived578 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c578 := by
  apply localUnsat_implies_entails f578 [c552, c550, c577, c60, c25, c238] c578 unsat578 (by rfl) a
  have h0 : Entails.eval a c552 := derived552 a h
  have h1 : Entails.eval a c550 := derived550 a h
  have h2 : Entails.eval a c577 := derived577 a h
  have h3 : Entails.eval a c60 := h 59 (by decide)
  have h4 : Entails.eval a c25 := h 24 (by decide)
  have h5 : Entails.eval a c238 := h 237 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c579 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨56, by decide⟩, true), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨4, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f579 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c97, some c98, some c89, some c238, some c376, some c34, some c549, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p579 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked579 : lratChecker f579 p579 = .success := by decide +kernel
theorem unsat579 : Unsatisfiable (PosFin 57) f579 := by
  apply lratCheckerSound f579 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p579
  · intro a ha; simp [p579] at ha; subst a; trivial
  · exact checked579
theorem derived579 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c579 := by
  apply localUnsat_implies_entails f579 [c547, c97, c98, c89, c238, c376, c34, c549] c579 unsat579 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c97 := h 96 (by decide)
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c89 := h 88 (by decide)
  have h4 : Entails.eval a c238 := h 237 (by decide)
  have h5 : Entails.eval a c376 := derived376 a h
  have h6 : Entails.eval a c34 := h 33 (by decide)
  have h7 : Entails.eval a c549 := derived549 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c580 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨3, by decide⟩, true), (⟨39, by decide⟩, false), (⟨40, by decide⟩, false), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f580 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c291, some c294, some c66, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p580 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked580 : lratChecker f580 p580 = .success := by decide +kernel
theorem unsat580 : Unsatisfiable (PosFin 57) f580 := by
  apply lratCheckerSound f580 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p580
  · intro a ha; simp [p580] at ha; subst a; trivial
  · exact checked580
theorem derived580 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c580 := by
  apply localUnsat_implies_entails f580 [c291, c294, c66] c580 unsat580 (by rfl) a
  have h0 : Entails.eval a c291 := h 290 (by decide)
  have h1 : Entails.eval a c294 := h 293 (by decide)
  have h2 : Entails.eval a c66 := h 65 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c581 : DefaultClause 57 := directClause [(⟨50, by decide⟩, false), (⟨15, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f581 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c229, some c168, some c199, some c103, some c243, some c46, some c108, some (DefaultClause.unit (⟨50, by decide⟩, true)), some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p581 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8]]
theorem checked581 : lratChecker f581 p581 = .success := by decide +kernel
theorem unsat581 : Unsatisfiable (PosFin 57) f581 := by
  apply lratCheckerSound f581 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p581
  · intro a ha; simp [p581] at ha; subst a; trivial
  · exact checked581
theorem derived581 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c581 := by
  apply localUnsat_implies_entails f581 [c547, c229, c168, c199, c103, c243, c46, c108] c581 unsat581 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c229 := h 228 (by decide)
  have h2 : Entails.eval a c168 := h 167 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c103 := h 102 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  have h6 : Entails.eval a c46 := h 45 (by decide)
  have h7 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c582 : DefaultClause 57 := directClause [(⟨15, by decide⟩, true), (⟨33, by decide⟩, true), (⟨14, by decide⟩, false), (⟨7, by decide⟩, false), (⟨54, by decide⟩, false), (⟨22, by decide⟩, false), (⟨1, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f582 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c581, some c280, some c223, some c162, some c199, some c102, some c248, some c40, some c108, some (DefaultClause.unit (⟨15, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨14, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p582 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked582 : lratChecker f582 p582 = .success := by decide +kernel
theorem unsat582 : Unsatisfiable (PosFin 57) f582 := by
  apply lratCheckerSound f582 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p582
  · intro a ha; simp [p582] at ha; subst a; trivial
  · exact checked582
theorem derived582 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c582 := by
  apply localUnsat_implies_entails f582 [c581, c280, c223, c162, c199, c102, c248, c40, c108] c582 unsat582 (by rfl) a
  have h0 : Entails.eval a c581 := derived581 a h
  have h1 : Entails.eval a c280 := h 279 (by decide)
  have h2 : Entails.eval a c223 := h 222 (by decide)
  have h3 : Entails.eval a c162 := h 161 (by decide)
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c102 := h 101 (by decide)
  have h6 : Entails.eval a c248 := h 247 (by decide)
  have h7 : Entails.eval a c40 := h 39 (by decide)
  have h8 : Entails.eval a c108 := h 107 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c583 : DefaultClause 57 := directClause [(⟨4, by decide⟩, false), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f583 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c98, some c97, some c550, some c552, some c567, some c61, some c578, some c579, some c96, some c561, some c580, some c582, some c151, some c68, some c66, some c300, some (DefaultClause.unit (⟨4, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p583 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]]
theorem checked583 : lratChecker f583 p583 = .success := by decide +kernel
theorem unsat583 : Unsatisfiable (PosFin 57) f583 := by
  apply lratCheckerSound f583 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p583
  · intro a ha; simp [p583] at ha; subst a; trivial
  · exact checked583
theorem derived583 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c583 := by
  apply localUnsat_implies_entails f583 [c547, c98, c97, c550, c552, c567, c61, c578, c579, c96, c561, c580, c582, c151, c68, c66, c300] c583 unsat583 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c98 := h 97 (by decide)
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c550 := derived550 a h
  have h4 : Entails.eval a c552 := derived552 a h
  have h5 : Entails.eval a c567 := derived567 a h
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c578 := derived578 a h
  have h8 : Entails.eval a c579 := derived579 a h
  have h9 : Entails.eval a c96 := h 95 (by decide)
  have h10 : Entails.eval a c561 := derived561 a h
  have h11 : Entails.eval a c580 := derived580 a h
  have h12 : Entails.eval a c582 := derived582 a h
  have h13 : Entails.eval a c151 := h 150 (by decide)
  have h14 : Entails.eval a c68 := h 67 (by decide)
  have h15 : Entails.eval a c66 := h 65 (by decide)
  have h16 : Entails.eval a c300 := h 299 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c584 : DefaultClause 57 := directClause [(⟨20, by decide⟩, false), (⟨22, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f584 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c247, some c241, some c199, some (DefaultClause.unit (⟨20, by decide⟩, true)), some (DefaultClause.unit (⟨22, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p584 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked584 : lratChecker f584 p584 = .success := by decide +kernel
theorem unsat584 : Unsatisfiable (PosFin 57) f584 := by
  apply lratCheckerSound f584 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p584
  · intro a ha; simp [p584] at ha; subst a; trivial
  · exact checked584
theorem derived584 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c584 := by
  apply localUnsat_implies_entails f584 [c247, c241, c199] c584 unsat584 (by rfl) a
  have h0 : Entails.eval a c247 := h 246 (by decide)
  have h1 : Entails.eval a c241 := h 240 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c585 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨40, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f585 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c300, some c301, some c65, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p585 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked585 : lratChecker f585 p585 = .success := by decide +kernel
theorem unsat585 : Unsatisfiable (PosFin 57) f585 := by
  apply lratCheckerSound f585 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p585
  · intro a ha; simp [p585] at ha; subst a; trivial
  · exact checked585
theorem derived585 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c585 := by
  apply localUnsat_implies_entails f585 [c300, c301, c65] c585 unsat585 (by rfl) a
  have h0 : Entails.eval a c300 := h 299 (by decide)
  have h1 : Entails.eval a c301 := h 300 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c586 : DefaultClause 57 := directClause [(⟨52, by decide⟩, false), (⟨33, by decide⟩, true), (⟨54, by decide⟩, false), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f586 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c323, some c317, some c280, some (DefaultClause.unit (⟨52, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p586 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked586 : lratChecker f586 p586 = .success := by decide +kernel
theorem unsat586 : Unsatisfiable (PosFin 57) f586 := by
  apply lratCheckerSound f586 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p586
  · intro a ha; simp [p586] at ha; subst a; trivial
  · exact checked586
theorem derived586 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c586 := by
  apply localUnsat_implies_entails f586 [c323, c317, c280] c586 unsat586 (by rfl) a
  have h0 : Entails.eval a c323 := h 322 (by decide)
  have h1 : Entails.eval a c317 := h 316 (by decide)
  have h2 : Entails.eval a c280 := h 279 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c587 : DefaultClause 57 := directClause [(⟨49, by decide⟩, true), (⟨51, by decide⟩, false), (⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f587 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c280, some c281, some c320, some (DefaultClause.unit (⟨49, by decide⟩, false)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p587 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked587 : lratChecker f587 p587 = .success := by decide +kernel
theorem unsat587 : Unsatisfiable (PosFin 57) f587 := by
  apply lratCheckerSound f587 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p587
  · intro a ha; simp [p587] at ha; subst a; trivial
  · exact checked587
theorem derived587 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c587 := by
  apply localUnsat_implies_entails f587 [c280, c281, c320] c587 unsat587 (by rfl) a
  have h0 : Entails.eval a c280 := h 279 (by decide)
  have h1 : Entails.eval a c281 := h 280 (by decide)
  have h2 : Entails.eval a c320 := h 319 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c588 : DefaultClause 57 := directClause [(⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨51, by decide⟩, false), (⟨54, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f588 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c223, some c221, some c31, some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false))]
def p588 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked588 : lratChecker f588 p588 = .success := by decide +kernel
theorem unsat588 : Unsatisfiable (PosFin 57) f588 := by
  apply lratCheckerSound f588 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p588
  · intro a ha; simp [p588] at ha; subst a; trivial
  · exact checked588
theorem derived588 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c588 := by
  apply localUnsat_implies_entails f588 [c223, c221, c31] c588 unsat588 (by rfl) a
  have h0 : Entails.eval a c223 := h 222 (by decide)
  have h1 : Entails.eval a c221 := h 220 (by decide)
  have h2 : Entails.eval a c31 := h 30 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c589 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨37, by decide⟩, true), (⟨54, by decide⟩, false), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f589 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c96, some c99, some c586, some c83, some c587, some c588, some c199, some c200, some c246, some c244, some c30, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨54, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p589 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]]
theorem checked589 : lratChecker f589 p589 = .success := by decide +kernel
theorem unsat589 : Unsatisfiable (PosFin 57) f589 := by
  apply lratCheckerSound f589 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p589
  · intro a ha; simp [p589] at ha; subst a; trivial
  · exact checked589
theorem derived589 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c589 := by
  apply localUnsat_implies_entails f589 [c547, c96, c99, c586, c83, c587, c588, c199, c200, c246, c244, c30] c589 unsat589 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c586 := derived586 a h
  have h4 : Entails.eval a c83 := h 82 (by decide)
  have h5 : Entails.eval a c587 := derived587 a h
  have h6 : Entails.eval a c588 := derived588 a h
  have h7 : Entails.eval a c199 := h 198 (by decide)
  have h8 : Entails.eval a c200 := h 199 (by decide)
  have h9 : Entails.eval a c246 := h 245 (by decide)
  have h10 : Entails.eval a c244 := h 243 (by decide)
  have h11 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c590 : DefaultClause 57 := directClause [(⟨56, by decide⟩, true), (⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f590 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c96, some c99, some c61, some c88, some c585, some c589, some c291, some c293, some c65, some (DefaultClause.unit (⟨56, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p590 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked590 : lratChecker f590 p590 = .success := by decide +kernel
theorem unsat590 : Unsatisfiable (PosFin 57) f590 := by
  apply lratCheckerSound f590 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p590
  · intro a ha; simp [p590] at ha; subst a; trivial
  · exact checked590
theorem derived590 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c590 := by
  apply localUnsat_implies_entails f590 [c547, c96, c99, c61, c88, c585, c589, c291, c293, c65] c590 unsat590 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c96 := h 95 (by decide)
  have h2 : Entails.eval a c99 := h 98 (by decide)
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c88 := h 87 (by decide)
  have h5 : Entails.eval a c585 := derived585 a h
  have h6 : Entails.eval a c589 := derived589 a h
  have h7 : Entails.eval a c291 := h 290 (by decide)
  have h8 : Entails.eval a c293 := h 292 (by decide)
  have h9 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c591 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f591 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c291, some c293, some c65, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p591 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked591 : lratChecker f591 p591 = .success := by decide +kernel
theorem unsat591 : Unsatisfiable (PosFin 57) f591 := by
  apply lratCheckerSound f591 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p591
  · intro a ha; simp [p591] at ha; subst a; trivial
  · exact checked591
theorem derived591 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c591 := by
  apply localUnsat_implies_entails f591 [c291, c293, c65] c591 unsat591 (by rfl) a
  have h0 : Entails.eval a c291 := h 290 (by decide)
  have h1 : Entails.eval a c293 := h 292 (by decide)
  have h2 : Entails.eval a c65 := h 64 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c592 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨56, by decide⟩, false), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f592 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c591, some c26, some c70, some c412, some c292, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p592 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked592 : lratChecker f592 p592 = .success := by decide +kernel
theorem unsat592 : Unsatisfiable (PosFin 57) f592 := by
  apply lratCheckerSound f592 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p592
  · intro a ha; simp [p592] at ha; subst a; trivial
  · exact checked592
theorem derived592 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c592 := by
  apply localUnsat_implies_entails f592 [c591, c26, c70, c412, c292] c592 unsat592 (by rfl) a
  have h0 : Entails.eval a c591 := derived591 a h
  have h1 : Entails.eval a c26 := h 25 (by decide)
  have h2 : Entails.eval a c70 := h 69 (by decide)
  have h3 : Entails.eval a c412 := derived412 a h
  have h4 : Entails.eval a c292 := h 291 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c593 : DefaultClause 57 := directClause [(⟨19, by decide⟩, true), (⟨33, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f593 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c31, some c30, some c584, some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p593 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked593 : lratChecker f593 p593 = .success := by decide +kernel
theorem unsat593 : Unsatisfiable (PosFin 57) f593 := by
  apply lratCheckerSound f593 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p593
  · intro a ha; simp [p593] at ha; subst a; trivial
  · exact checked593
theorem derived593 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c593 := by
  apply localUnsat_implies_entails f593 [c31, c30, c584] c593 unsat593 (by rfl) a
  have h0 : Entails.eval a c31 := h 30 (by decide)
  have h1 : Entails.eval a c30 := h 29 (by decide)
  have h2 : Entails.eval a c584 := derived584 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c594 : DefaultClause 57 := directClause [(⟨51, by decide⟩, true), (⟨33, by decide⟩, true), (⟨3, by decide⟩, true), (⟨6, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f594 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c84, some c83, some c586, some (DefaultClause.unit (⟨51, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p594 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked594 : lratChecker f594 p594 = .success := by decide +kernel
theorem unsat594 : Unsatisfiable (PosFin 57) f594 := by
  apply lratCheckerSound f594 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p594
  · intro a ha; simp [p594] at ha; subst a; trivial
  · exact checked594
theorem derived594 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c594 := by
  apply localUnsat_implies_entails f594 [c84, c83, c586] c594 unsat594 (by rfl) a
  have h0 : Entails.eval a c84 := h 83 (by decide)
  have h1 : Entails.eval a c83 := h 82 (by decide)
  have h2 : Entails.eval a c586 := derived586 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c595 : DefaultClause 57 := directClause [(⟨7, by decide⟩, false), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f595 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c99, some c96, some c590, some c592, some c593, some c594, some c233, some c325, some c316, some c26, some c281, some c585, some (DefaultClause.unit (⟨7, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p595 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked595 : lratChecker f595 p595 = .success := by decide +kernel
theorem unsat595 : Unsatisfiable (PosFin 57) f595 := by
  apply lratCheckerSound f595 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p595
  · intro a ha; simp [p595] at ha; subst a; trivial
  · exact checked595
theorem derived595 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c595 := by
  apply localUnsat_implies_entails f595 [c547, c99, c96, c590, c592, c593, c594, c233, c325, c316, c26, c281, c585] c595 unsat595 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c99 := h 98 (by decide)
  have h2 : Entails.eval a c96 := h 95 (by decide)
  have h3 : Entails.eval a c590 := derived590 a h
  have h4 : Entails.eval a c592 := derived592 a h
  have h5 : Entails.eval a c593 := derived593 a h
  have h6 : Entails.eval a c594 := derived594 a h
  have h7 : Entails.eval a c233 := h 232 (by decide)
  have h8 : Entails.eval a c325 := h 324 (by decide)
  have h9 : Entails.eval a c316 := h 315 (by decide)
  have h10 : Entails.eval a c26 := h 25 (by decide)
  have h11 : Entails.eval a c281 := h 280 (by decide)
  have h12 : Entails.eval a c585 := derived585 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c596 : DefaultClause 57 := directClause [(⟨51, by decide⟩, false), (⟨37, by decide⟩, true), (⟨56, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f596 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c316, some c587, some (DefaultClause.unit (⟨51, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p596 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked596 : lratChecker f596 p596 = .success := by decide +kernel
theorem unsat596 : Unsatisfiable (PosFin 57) f596 := by
  apply lratCheckerSound f596 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p596
  · intro a ha; simp [p596] at ha; subst a; trivial
  · exact checked596
theorem derived596 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c596 := by
  apply localUnsat_implies_entails f596 [c316, c587] c596 unsat596 (by rfl) a
  have h0 : Entails.eval a c316 := h 315 (by decide)
  have h1 : Entails.eval a c587 := derived587 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c597 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨56, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f597 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c8, some c585, some c596, some c56, some c83, some c146, some c175, some c12, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p597 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked597 : lratChecker f597 p597 = .success := by decide +kernel
theorem unsat597 : Unsatisfiable (PosFin 57) f597 := by
  apply lratCheckerSound f597 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p597
  · intro a ha; simp [p597] at ha; subst a; trivial
  · exact checked597
theorem derived597 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c597 := by
  apply localUnsat_implies_entails f597 [c26, c8, c585, c596, c56, c83, c146, c175, c12] c597 unsat597 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c585 := derived585 a h
  have h3 : Entails.eval a c596 := derived596 a h
  have h4 : Entails.eval a c56 := h 55 (by decide)
  have h5 : Entails.eval a c83 := h 82 (by decide)
  have h6 : Entails.eval a c146 := h 145 (by decide)
  have h7 : Entails.eval a c175 := h 174 (by decide)
  have h8 : Entails.eval a c12 := h 11 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c598 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨3, by decide⟩, true), (⟨33, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f598 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c595, some c597, some c412, some c494, some c85, some c318, some c236, some c280, some c30, some c32, some c508, some c239, some c199, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p598 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]]
theorem checked598 : lratChecker f598 p598 = .success := by decide +kernel
theorem unsat598 : Unsatisfiable (PosFin 57) f598 := by
  apply lratCheckerSound f598 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p598
  · intro a ha; simp [p598] at ha; subst a; trivial
  · exact checked598
theorem derived598 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c598 := by
  apply localUnsat_implies_entails f598 [c583, c595, c597, c412, c494, c85, c318, c236, c280, c30, c32, c508, c239, c199] c598 unsat598 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c597 := derived597 a h
  have h3 : Entails.eval a c412 := derived412 a h
  have h4 : Entails.eval a c494 := derived494 a h
  have h5 : Entails.eval a c85 := h 84 (by decide)
  have h6 : Entails.eval a c318 := h 317 (by decide)
  have h7 : Entails.eval a c236 := h 235 (by decide)
  have h8 : Entails.eval a c280 := h 279 (by decide)
  have h9 : Entails.eval a c30 := h 29 (by decide)
  have h10 : Entails.eval a c32 := h 31 (by decide)
  have h11 : Entails.eval a c508 := derived508 a h
  have h12 : Entails.eval a c239 := h 238 (by decide)
  have h13 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c599 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨37, by decide⟩, true), (⟨3, by decide⟩, true), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f599 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c426, some c200, some c240, some c242, some c30, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨37, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p599 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked599 : lratChecker f599 p599 = .success := by decide +kernel
theorem unsat599 : Unsatisfiable (PosFin 57) f599 := by
  apply lratCheckerSound f599 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p599
  · intro a ha; simp [p599] at ha; subst a; trivial
  · exact checked599
theorem derived599 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c599 := by
  apply localUnsat_implies_entails f599 [c426, c200, c240, c242, c30] c599 unsat599 (by rfl) a
  have h0 : Entails.eval a c426 := derived426 a h
  have h1 : Entails.eval a c200 := h 199 (by decide)
  have h2 : Entails.eval a c240 := h 239 (by decide)
  have h3 : Entails.eval a c242 := h 241 (by decide)
  have h4 : Entails.eval a c30 := h 29 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c600 : DefaultClause 57 := directClause [(⟨3, by decide⟩, true), (⟨33, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f600 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c595, some c598, some c61, some c89, some c585, some c480, some c56, some c599, some c8, some c36, some c146, some c3, some c239, some c245, some c199, some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p600 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]]
theorem checked600 : lratChecker f600 p600 = .success := by decide +kernel
theorem unsat600 : Unsatisfiable (PosFin 57) f600 := by
  apply lratCheckerSound f600 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p600
  · intro a ha; simp [p600] at ha; subst a; trivial
  · exact checked600
theorem derived600 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c600 := by
  apply localUnsat_implies_entails f600 [c583, c595, c598, c61, c89, c585, c480, c56, c599, c8, c36, c146, c3, c239, c245, c199] c600 unsat600 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c598 := derived598 a h
  have h3 : Entails.eval a c61 := h 60 (by decide)
  have h4 : Entails.eval a c89 := h 88 (by decide)
  have h5 : Entails.eval a c585 := derived585 a h
  have h6 : Entails.eval a c480 := derived480 a h
  have h7 : Entails.eval a c56 := h 55 (by decide)
  have h8 : Entails.eval a c599 := derived599 a h
  have h9 : Entails.eval a c8 := h 7 (by decide)
  have h10 : Entails.eval a c36 := h 35 (by decide)
  have h11 : Entails.eval a c146 := h 145 (by decide)
  have h12 : Entails.eval a c3 := h 2 (by decide)
  have h13 : Entails.eval a c239 := h 238 (by decide)
  have h14 : Entails.eval a c245 := h 244 (by decide)
  have h15 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c601 : DefaultClause 57 := directClause [(⟨19, by decide⟩, false), (⟨23, by decide⟩, false), (⟨33, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f601 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c239, some c245, some c199, some (DefaultClause.unit (⟨19, by decide⟩, true)), some (DefaultClause.unit (⟨23, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p601 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked601 : lratChecker f601 p601 = .success := by decide +kernel
theorem unsat601 : Unsatisfiable (PosFin 57) f601 := by
  apply lratCheckerSound f601 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p601
  · intro a ha; simp [p601] at ha; subst a; trivial
  · exact checked601
theorem derived601 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c601 := by
  apply localUnsat_implies_entails f601 [c239, c245, c199] c601 unsat601 (by rfl) a
  have h0 : Entails.eval a c239 := h 238 (by decide)
  have h1 : Entails.eval a c245 := h 244 (by decide)
  have h2 : Entails.eval a c199 := h 198 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c602 : DefaultClause 57 := directClause [(⟨20, by decide⟩, true), (⟨16, by decide⟩, false), (⟨40, by decide⟩, false), (⟨4, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f602 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c4, some c22, some c149, some (DefaultClause.unit (⟨20, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨4, by decide⟩, false))]
def p602 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked602 : lratChecker f602 p602 = .success := by decide +kernel
theorem unsat602 : Unsatisfiable (PosFin 57) f602 := by
  apply lratCheckerSound f602 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p602
  · intro a ha; simp [p602] at ha; subst a; trivial
  · exact checked602
theorem derived602 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c602 := by
  apply localUnsat_implies_entails f602 [c4, c22, c149] c602 unsat602 (by rfl) a
  have h0 : Entails.eval a c4 := h 3 (by decide)
  have h1 : Entails.eval a c22 := h 21 (by decide)
  have h2 : Entails.eval a c149 := h 148 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c603 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨16, by decide⟩, false), (⟨40, by decide⟩, false), (⟨5, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f603 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c23, some c5, some c150, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false))]
def p603 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked603 : lratChecker f603 p603 = .success := by decide +kernel
theorem unsat603 : Unsatisfiable (PosFin 57) f603 := by
  apply lratCheckerSound f603 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p603
  · intro a ha; simp [p603] at ha; subst a; trivial
  · exact checked603
theorem derived603 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c603 := by
  apply localUnsat_implies_entails f603 [c23, c5, c150] c603 unsat603 (by rfl) a
  have h0 : Entails.eval a c23 := h 22 (by decide)
  have h1 : Entails.eval a c5 := h 4 (by decide)
  have h2 : Entails.eval a c150 := h 149 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c604 : DefaultClause 57 := directClause [(⟨37, by decide⟩, false), (⟨6, by decide⟩, false), (⟨19, by decide⟩, true), (⟨16, by decide⟩, false), (⟨40, by decide⟩, false), (⟨5, by decide⟩, true), (⟨33, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f604 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c602, some c603, some c246, some c199, some c584, some c547, some c300, some c301, some c150, some c203, some c57, some c67, some c16, some c234, some c222, some c151, some c87, some c280, some c107, some c169, some c45, some c103, some (DefaultClause.unit (⟨37, by decide⟩, true)), some (DefaultClause.unit (⟨6, by decide⟩, true)), some (DefaultClause.unit (⟨19, by decide⟩, false)), some (DefaultClause.unit (⟨16, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p604 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]]
theorem checked604 : lratChecker f604 p604 = .success := by decide +kernel
theorem unsat604 : Unsatisfiable (PosFin 57) f604 := by
  apply lratCheckerSound f604 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p604
  · intro a ha; simp [p604] at ha; subst a; trivial
  · exact checked604
theorem derived604 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c604 := by
  apply localUnsat_implies_entails f604 [c602, c603, c246, c199, c584, c547, c300, c301, c150, c203, c57, c67, c16, c234, c222, c151, c87, c280, c107, c169, c45, c103] c604 unsat604 (by rfl) a
  have h0 : Entails.eval a c602 := derived602 a h
  have h1 : Entails.eval a c603 := derived603 a h
  have h2 : Entails.eval a c246 := h 245 (by decide)
  have h3 : Entails.eval a c199 := h 198 (by decide)
  have h4 : Entails.eval a c584 := derived584 a h
  have h5 : Entails.eval a c547 := derived547 a h
  have h6 : Entails.eval a c300 := h 299 (by decide)
  have h7 : Entails.eval a c301 := h 300 (by decide)
  have h8 : Entails.eval a c150 := h 149 (by decide)
  have h9 : Entails.eval a c203 := h 202 (by decide)
  have h10 : Entails.eval a c57 := h 56 (by decide)
  have h11 : Entails.eval a c67 := h 66 (by decide)
  have h12 : Entails.eval a c16 := h 15 (by decide)
  have h13 : Entails.eval a c234 := h 233 (by decide)
  have h14 : Entails.eval a c222 := h 221 (by decide)
  have h15 : Entails.eval a c151 := h 150 (by decide)
  have h16 : Entails.eval a c87 := h 86 (by decide)
  have h17 : Entails.eval a c280 := h 279 (by decide)
  have h18 : Entails.eval a c107 := h 106 (by decide)
  have h19 : Entails.eval a c169 := h 168 (by decide)
  have h20 : Entails.eval a c45 := h 44 (by decide)
  have h21 : Entails.eval a c103 := h 102 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c605 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f605 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c95, some c595, some c26, some c8, some c36, some c601, some c602, some c603, some c584, some c246, some c35, some c199, some c604, some c58, some c234, some c57, some c85, some c149, some c224, some c14, some c280, some c169, some c103, some c42, some c45, some c194, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p605 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked605 : lratChecker f605 p605 = .success := by decide +kernel
theorem unsat605 : Unsatisfiable (PosFin 57) f605 := by
  apply lratCheckerSound f605 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p605
  · intro a ha; simp [p605] at ha; subst a; trivial
  · exact checked605
theorem derived605 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c605 := by
  apply localUnsat_implies_entails f605 [c547, c95, c595, c26, c8, c36, c601, c602, c603, c584, c246, c35, c199, c604, c58, c234, c57, c85, c149, c224, c14, c280, c169, c103, c42, c45, c194] c605 unsat605 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c95 := h 94 (by decide)
  have h2 : Entails.eval a c595 := derived595 a h
  have h3 : Entails.eval a c26 := h 25 (by decide)
  have h4 : Entails.eval a c8 := h 7 (by decide)
  have h5 : Entails.eval a c36 := h 35 (by decide)
  have h6 : Entails.eval a c601 := derived601 a h
  have h7 : Entails.eval a c602 := derived602 a h
  have h8 : Entails.eval a c603 := derived603 a h
  have h9 : Entails.eval a c584 := derived584 a h
  have h10 : Entails.eval a c246 := h 245 (by decide)
  have h11 : Entails.eval a c35 := h 34 (by decide)
  have h12 : Entails.eval a c199 := h 198 (by decide)
  have h13 : Entails.eval a c604 := derived604 a h
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c234 := h 233 (by decide)
  have h16 : Entails.eval a c57 := h 56 (by decide)
  have h17 : Entails.eval a c85 := h 84 (by decide)
  have h18 : Entails.eval a c149 := h 148 (by decide)
  have h19 : Entails.eval a c224 := h 223 (by decide)
  have h20 : Entails.eval a c14 := h 13 (by decide)
  have h21 : Entails.eval a c280 := h 279 (by decide)
  have h22 : Entails.eval a c169 := h 168 (by decide)
  have h23 : Entails.eval a c103 := h 102 (by decide)
  have h24 : Entails.eval a c42 := h 41 (by decide)
  have h25 : Entails.eval a c45 := h 44 (by decide)
  have h26 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c606 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f606 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c605, some c199, some c242, some c22, some c547, some c95, some c595, some c423, some c243, some c601, some c602, some c301, some c18, some c23, some c58, some c237, some c89, some c548, some c224, some c88, some c280, some c169, some c103, some c42, some c45, some c194, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p606 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]]
theorem checked606 : lratChecker f606 p606 = .success := by decide +kernel
theorem unsat606 : Unsatisfiable (PosFin 57) f606 := by
  apply lratCheckerSound f606 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p606
  · intro a ha; simp [p606] at ha; subst a; trivial
  · exact checked606
theorem derived606 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c606 := by
  apply localUnsat_implies_entails f606 [c605, c199, c242, c22, c547, c95, c595, c423, c243, c601, c602, c301, c18, c23, c58, c237, c89, c548, c224, c88, c280, c169, c103, c42, c45, c194] c606 unsat606 (by rfl) a
  have h0 : Entails.eval a c605 := derived605 a h
  have h1 : Entails.eval a c199 := h 198 (by decide)
  have h2 : Entails.eval a c242 := h 241 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c547 := derived547 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  have h6 : Entails.eval a c595 := derived595 a h
  have h7 : Entails.eval a c423 := derived423 a h
  have h8 : Entails.eval a c243 := h 242 (by decide)
  have h9 : Entails.eval a c601 := derived601 a h
  have h10 : Entails.eval a c602 := derived602 a h
  have h11 : Entails.eval a c301 := h 300 (by decide)
  have h12 : Entails.eval a c18 := h 17 (by decide)
  have h13 : Entails.eval a c23 := h 22 (by decide)
  have h14 : Entails.eval a c58 := h 57 (by decide)
  have h15 : Entails.eval a c237 := h 236 (by decide)
  have h16 : Entails.eval a c89 := h 88 (by decide)
  have h17 : Entails.eval a c548 := derived548 a h
  have h18 : Entails.eval a c224 := h 223 (by decide)
  have h19 : Entails.eval a c88 := h 87 (by decide)
  have h20 : Entails.eval a c280 := h 279 (by decide)
  have h21 : Entails.eval a c169 := h 168 (by decide)
  have h22 : Entails.eval a c103 := h 102 (by decide)
  have h23 : Entails.eval a c42 := h 41 (by decide)
  have h24 : Entails.eval a c45 := h 44 (by decide)
  have h25 : Entails.eval a c194 := h 193 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c607 : DefaultClause 57 := directClause [(⟨18, by decide⟩, true), (⟨3, by decide⟩, false), (⟨33, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f607 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c605, some c547, some c95, some c595, some c199, some c242, some c22, some c606, some c61, some c494, some c225, some c85, some c87, some c280, some c322, some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p607 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]]
theorem checked607 : lratChecker f607 p607 = .success := by decide +kernel
theorem unsat607 : Unsatisfiable (PosFin 57) f607 := by
  apply lratCheckerSound f607 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p607
  · intro a ha; simp [p607] at ha; subst a; trivial
  · exact checked607
theorem derived607 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c607 := by
  apply localUnsat_implies_entails f607 [c605, c547, c95, c595, c199, c242, c22, c606, c61, c494, c225, c85, c87, c280, c322] c607 unsat607 (by rfl) a
  have h0 : Entails.eval a c605 := derived605 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c95 := h 94 (by decide)
  have h3 : Entails.eval a c595 := derived595 a h
  have h4 : Entails.eval a c199 := h 198 (by decide)
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c22 := h 21 (by decide)
  have h7 : Entails.eval a c606 := derived606 a h
  have h8 : Entails.eval a c61 := h 60 (by decide)
  have h9 : Entails.eval a c494 := derived494 a h
  have h10 : Entails.eval a c225 := h 224 (by decide)
  have h11 : Entails.eval a c85 := h 84 (by decide)
  have h12 : Entails.eval a c87 := h 86 (by decide)
  have h13 : Entails.eval a c280 := h 279 (by decide)
  have h14 : Entails.eval a c322 := h 321 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c608 : DefaultClause 57 := directClause [(⟨56, by decide⟩, false), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f608 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c412, some c494, some c85, some c87, some c326, some (DefaultClause.unit (⟨56, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p608 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5]]
theorem checked608 : lratChecker f608 p608 = .success := by decide +kernel
theorem unsat608 : Unsatisfiable (PosFin 57) f608 := by
  apply lratCheckerSound f608 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p608
  · intro a ha; simp [p608] at ha; subst a; trivial
  · exact checked608
theorem derived608 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c608 := by
  apply localUnsat_implies_entails f608 [c412, c494, c85, c87, c326] c608 unsat608 (by rfl) a
  have h0 : Entails.eval a c412 := derived412 a h
  have h1 : Entails.eval a c494 := derived494 a h
  have h2 : Entails.eval a c85 := h 84 (by decide)
  have h3 : Entails.eval a c87 := h 86 (by decide)
  have h4 : Entails.eval a c326 := h 325 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
def c609 : DefaultClause 57 := directClause [(⟨36, by decide⟩, false), (⟨33, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f609 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c595, some c547, some c600, some c95, some c605, some c608, some c89, some c607, some c423, some c230, some c280, some c319, some c88, some c224, some c61, some c248, some c601, some c301, some c23, some c69, some c250, some c4, some c602, some c18, some c489, some c481, some c148, some c203, some (DefaultClause.unit (⟨36, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p609 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked609 : lratChecker f609 p609 = .success := by decide +kernel
theorem unsat609 : Unsatisfiable (PosFin 57) f609 := by
  apply lratCheckerSound f609 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p609
  · intro a ha; simp [p609] at ha; subst a; trivial
  · exact checked609
theorem derived609 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c609 := by
  apply localUnsat_implies_entails f609 [c583, c595, c547, c600, c95, c605, c608, c89, c607, c423, c230, c280, c319, c88, c224, c61, c248, c601, c301, c23, c69, c250, c4, c602, c18, c489, c481, c148, c203] c609 unsat609 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c547 := derived547 a h
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c605 := derived605 a h
  have h6 : Entails.eval a c608 := derived608 a h
  have h7 : Entails.eval a c89 := h 88 (by decide)
  have h8 : Entails.eval a c607 := derived607 a h
  have h9 : Entails.eval a c423 := derived423 a h
  have h10 : Entails.eval a c230 := h 229 (by decide)
  have h11 : Entails.eval a c280 := h 279 (by decide)
  have h12 : Entails.eval a c319 := h 318 (by decide)
  have h13 : Entails.eval a c88 := h 87 (by decide)
  have h14 : Entails.eval a c224 := h 223 (by decide)
  have h15 : Entails.eval a c61 := h 60 (by decide)
  have h16 : Entails.eval a c248 := h 247 (by decide)
  have h17 : Entails.eval a c601 := derived601 a h
  have h18 : Entails.eval a c301 := h 300 (by decide)
  have h19 : Entails.eval a c23 := h 22 (by decide)
  have h20 : Entails.eval a c69 := h 68 (by decide)
  have h21 : Entails.eval a c250 := h 249 (by decide)
  have h22 : Entails.eval a c4 := h 3 (by decide)
  have h23 : Entails.eval a c602 := derived602 a h
  have h24 : Entails.eval a c18 := h 17 (by decide)
  have h25 : Entails.eval a c489 := derived489 a h
  have h26 : Entails.eval a c481 := derived481 a h
  have h27 : Entails.eval a c148 := h 147 (by decide)
  have h28 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c610 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f610 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c583, some c595, some c547, some c600, some c95, some c605, some c423, some c601, some c607, some c248, some c608, some c61, some c89, some c230, some c280, some c224, some c319, some c88, some c609, some c22, some c67, some c250, some c23, some c603, some c300, some c18, some c203, some c489, some c151, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p610 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]]
theorem checked610 : lratChecker f610 p610 = .success := by decide +kernel
theorem unsat610 : Unsatisfiable (PosFin 57) f610 := by
  apply lratCheckerSound f610 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p610
  · intro a ha; simp [p610] at ha; subst a; trivial
  · exact checked610
theorem derived610 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c610 := by
  apply localUnsat_implies_entails f610 [c583, c595, c547, c600, c95, c605, c423, c601, c607, c248, c608, c61, c89, c230, c280, c224, c319, c88, c609, c22, c67, c250, c23, c603, c300, c18, c203, c489, c151] c610 unsat610 (by rfl) a
  have h0 : Entails.eval a c583 := derived583 a h
  have h1 : Entails.eval a c595 := derived595 a h
  have h2 : Entails.eval a c547 := derived547 a h
  have h3 : Entails.eval a c600 := derived600 a h
  have h4 : Entails.eval a c95 := h 94 (by decide)
  have h5 : Entails.eval a c605 := derived605 a h
  have h6 : Entails.eval a c423 := derived423 a h
  have h7 : Entails.eval a c601 := derived601 a h
  have h8 : Entails.eval a c607 := derived607 a h
  have h9 : Entails.eval a c248 := h 247 (by decide)
  have h10 : Entails.eval a c608 := derived608 a h
  have h11 : Entails.eval a c61 := h 60 (by decide)
  have h12 : Entails.eval a c89 := h 88 (by decide)
  have h13 : Entails.eval a c230 := h 229 (by decide)
  have h14 : Entails.eval a c280 := h 279 (by decide)
  have h15 : Entails.eval a c224 := h 223 (by decide)
  have h16 : Entails.eval a c319 := h 318 (by decide)
  have h17 : Entails.eval a c88 := h 87 (by decide)
  have h18 : Entails.eval a c609 := derived609 a h
  have h19 : Entails.eval a c22 := h 21 (by decide)
  have h20 : Entails.eval a c67 := h 66 (by decide)
  have h21 : Entails.eval a c250 := h 249 (by decide)
  have h22 : Entails.eval a c23 := h 22 (by decide)
  have h23 : Entails.eval a c603 := derived603 a h
  have h24 : Entails.eval a c300 := h 299 (by decide)
  have h25 : Entails.eval a c18 := h 17 (by decide)
  have h26 : Entails.eval a c203 := h 202 (by decide)
  have h27 : Entails.eval a c489 := derived489 a h
  have h28 : Entails.eval a c151 := h 150 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c611 : DefaultClause 57 := directClause [(⟨49, by decide⟩, false), (⟨55, by decide⟩, false), (⟨39, by decide⟩, false), (⟨33, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f611 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c319, some c315, some c462, some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨55, by decide⟩, true)), some (DefaultClause.unit (⟨39, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true))]
def p611 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3]]
theorem checked611 : lratChecker f611 p611 = .success := by decide +kernel
theorem unsat611 : Unsatisfiable (PosFin 57) f611 := by
  apply lratCheckerSound f611 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p611
  · intro a ha; simp [p611] at ha; subst a; trivial
  · exact checked611
theorem derived611 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c611 := by
  apply localUnsat_implies_entails f611 [c319, c315, c462] c611 unsat611 (by rfl) a
  have h0 : Entails.eval a c319 := h 318 (by decide)
  have h1 : Entails.eval a c315 := h 314 (by decide)
  have h2 : Entails.eval a c462 := derived462 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> assumption
def c612 : DefaultClause 57 := directClause [(⟨40, by decide⟩, false), (⟨24, by decide⟩, false), (⟨33, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f612 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c293, some c591, some c57, some c22, some c412, some c67, some c95, some c242, some c250, some c89, some c23, some c5, some c603, some c18, some c137, some c102, some c254, some c255, some c126, some c273, some c279, some c220, some c611, some c303, some c173, some c322, some c122, some c270, some c267, some c266, some c265, some c327, some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p612 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]]
theorem checked612 : lratChecker f612 p612 = .success := by decide +kernel
theorem unsat612 : Unsatisfiable (PosFin 57) f612 := by
  apply lratCheckerSound f612 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p612
  · intro a ha; simp [p612] at ha; subst a; trivial
  · exact checked612
theorem derived612 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c612 := by
  apply localUnsat_implies_entails f612 [c293, c591, c57, c22, c412, c67, c95, c242, c250, c89, c23, c5, c603, c18, c137, c102, c254, c255, c126, c273, c279, c220, c611, c303, c173, c322, c122, c270, c267, c266, c265, c327] c612 unsat612 (by rfl) a
  have h0 : Entails.eval a c293 := h 292 (by decide)
  have h1 : Entails.eval a c591 := derived591 a h
  have h2 : Entails.eval a c57 := h 56 (by decide)
  have h3 : Entails.eval a c22 := h 21 (by decide)
  have h4 : Entails.eval a c412 := derived412 a h
  have h5 : Entails.eval a c67 := h 66 (by decide)
  have h6 : Entails.eval a c95 := h 94 (by decide)
  have h7 : Entails.eval a c242 := h 241 (by decide)
  have h8 : Entails.eval a c250 := h 249 (by decide)
  have h9 : Entails.eval a c89 := h 88 (by decide)
  have h10 : Entails.eval a c23 := h 22 (by decide)
  have h11 : Entails.eval a c5 := h 4 (by decide)
  have h12 : Entails.eval a c603 := derived603 a h
  have h13 : Entails.eval a c18 := h 17 (by decide)
  have h14 : Entails.eval a c137 := h 136 (by decide)
  have h15 : Entails.eval a c102 := h 101 (by decide)
  have h16 : Entails.eval a c254 := h 253 (by decide)
  have h17 : Entails.eval a c255 := h 254 (by decide)
  have h18 : Entails.eval a c126 := h 125 (by decide)
  have h19 : Entails.eval a c273 := h 272 (by decide)
  have h20 : Entails.eval a c279 := h 278 (by decide)
  have h21 : Entails.eval a c220 := h 219 (by decide)
  have h22 : Entails.eval a c611 := derived611 a h
  have h23 : Entails.eval a c303 := h 302 (by decide)
  have h24 : Entails.eval a c173 := h 172 (by decide)
  have h25 : Entails.eval a c322 := h 321 (by decide)
  have h26 : Entails.eval a c122 := h 121 (by decide)
  have h27 : Entails.eval a c270 := h 269 (by decide)
  have h28 : Entails.eval a c267 := h 266 (by decide)
  have h29 : Entails.eval a c266 := h 265 (by decide)
  have h30 : Entails.eval a c265 := h 264 (by decide)
  have h31 : Entails.eval a c327 := derived327 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c613 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨33, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f613 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c612, some c61, some c415, some c608, some c95, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p613 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6]]
theorem checked613 : lratChecker f613 p613 = .success := by decide +kernel
theorem unsat613 : Unsatisfiable (PosFin 57) f613 := by
  apply lratCheckerSound f613 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p613
  · intro a ha; simp [p613] at ha; subst a; trivial
  · exact checked613
theorem derived613 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c613 := by
  apply localUnsat_implies_entails f613 [c382, c612, c61, c415, c608, c95] c613 unsat613 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c612 := derived612 a h
  have h2 : Entails.eval a c61 := h 60 (by decide)
  have h3 : Entails.eval a c415 := derived415 a h
  have h4 : Entails.eval a c608 := derived608 a h
  have h5 : Entails.eval a c95 := h 94 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c614 : DefaultClause 57 := directClause [(⟨17, by decide⟩, true), (⟨15, by decide⟩, false), (⟨13, by decide⟩, true), (⟨18, by decide⟩, true), (⟨9, by decide⟩, true), (⟨3, by decide⟩, false), (⟨40, by decide⟩, false), (⟨24, by decide⟩, true), (⟨33, by decide⟩, false), (⟨1, by decide⟩, false), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f614 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c95, some c102, some c110, some c255, some c37, some c187, some c184, some c192, some c130, some c15, some c45, some (DefaultClause.unit (⟨17, by decide⟩, false)), some (DefaultClause.unit (⟨15, by decide⟩, true)), some (DefaultClause.unit (⟨13, by decide⟩, false)), some (DefaultClause.unit (⟨18, by decide⟩, false)), some (DefaultClause.unit (⟨9, by decide⟩, false)), some (DefaultClause.unit (⟨3, by decide⟩, true)), some (DefaultClause.unit (⟨40, by decide⟩, true)), some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p614 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked614 : lratChecker f614 p614 = .success := by decide +kernel
theorem unsat614 : Unsatisfiable (PosFin 57) f614 := by
  apply lratCheckerSound f614 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p614
  · intro a ha; simp [p614] at ha; subst a; trivial
  · exact checked614
theorem derived614 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c614 := by
  apply localUnsat_implies_entails f614 [c95, c102, c110, c255, c37, c187, c184, c192, c130, c15, c45] c614 unsat614 (by rfl) a
  have h0 : Entails.eval a c95 := h 94 (by decide)
  have h1 : Entails.eval a c102 := h 101 (by decide)
  have h2 : Entails.eval a c110 := h 109 (by decide)
  have h3 : Entails.eval a c255 := h 254 (by decide)
  have h4 : Entails.eval a c37 := h 36 (by decide)
  have h5 : Entails.eval a c187 := h 186 (by decide)
  have h6 : Entails.eval a c184 := h 183 (by decide)
  have h7 : Entails.eval a c192 := h 191 (by decide)
  have h8 : Entails.eval a c130 := h 129 (by decide)
  have h9 : Entails.eval a c15 := h 14 (by decide)
  have h10 : Entails.eval a c45 := h 44 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c615 : DefaultClause 57 := directClause [(⟨1, by decide⟩, false), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f615 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c583, some c595, some c610, some c382, some c613, some c26, some c8, some c36, some c293, some c591, some c138, some c602, some c57, some c67, some c95, some c294, some c603, some c246, some c234, some c58, some c150, some c16, some c614, some c239, some c243, some c203, some (DefaultClause.unit (⟨1, by decide⟩, true)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p615 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]]
theorem checked615 : lratChecker f615 p615 = .success := by decide +kernel
theorem unsat615 : Unsatisfiable (PosFin 57) f615 := by
  apply lratCheckerSound f615 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p615
  · intro a ha; simp [p615] at ha; subst a; trivial
  · exact checked615
theorem derived615 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c615 := by
  apply localUnsat_implies_entails f615 [c547, c583, c595, c610, c382, c613, c26, c8, c36, c293, c591, c138, c602, c57, c67, c95, c294, c603, c246, c234, c58, c150, c16, c614, c239, c243, c203] c615 unsat615 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c583 := derived583 a h
  have h2 : Entails.eval a c595 := derived595 a h
  have h3 : Entails.eval a c610 := derived610 a h
  have h4 : Entails.eval a c382 := derived382 a h
  have h5 : Entails.eval a c613 := derived613 a h
  have h6 : Entails.eval a c26 := h 25 (by decide)
  have h7 : Entails.eval a c8 := h 7 (by decide)
  have h8 : Entails.eval a c36 := h 35 (by decide)
  have h9 : Entails.eval a c293 := h 292 (by decide)
  have h10 : Entails.eval a c591 := derived591 a h
  have h11 : Entails.eval a c138 := h 137 (by decide)
  have h12 : Entails.eval a c602 := derived602 a h
  have h13 : Entails.eval a c57 := h 56 (by decide)
  have h14 : Entails.eval a c67 := h 66 (by decide)
  have h15 : Entails.eval a c95 := h 94 (by decide)
  have h16 : Entails.eval a c294 := h 293 (by decide)
  have h17 : Entails.eval a c603 := derived603 a h
  have h18 : Entails.eval a c246 := h 245 (by decide)
  have h19 : Entails.eval a c234 := h 233 (by decide)
  have h20 : Entails.eval a c58 := h 57 (by decide)
  have h21 : Entails.eval a c150 := h 149 (by decide)
  have h22 : Entails.eval a c16 := h 15 (by decide)
  have h23 : Entails.eval a c614 := derived614 a h
  have h24 : Entails.eval a c239 := h 238 (by decide)
  have h25 : Entails.eval a c243 := h 242 (by decide)
  have h26 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c616 : DefaultClause 57 := directClause [(⟨33, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true), (⟨2, by decide⟩, false)] (by decide +kernel) (by decide +kernel)
def f616 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c382, some c613, some c26, some c8, some c36, some c293, some c138, some c67, some c1, some c294, some c239, some c243, some c203, some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true))]
def p616 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked616 : lratChecker f616 p616 = .success := by decide +kernel
theorem unsat616 : Unsatisfiable (PosFin 57) f616 := by
  apply lratCheckerSound f616 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p616
  · intro a ha; simp [p616] at ha; subst a; trivial
  · exact checked616
theorem derived616 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c616 := by
  apply localUnsat_implies_entails f616 [c382, c613, c26, c8, c36, c293, c138, c67, c1, c294, c239, c243, c203] c616 unsat616 (by rfl) a
  have h0 : Entails.eval a c382 := derived382 a h
  have h1 : Entails.eval a c613 := derived613 a h
  have h2 : Entails.eval a c26 := h 25 (by decide)
  have h3 : Entails.eval a c8 := h 7 (by decide)
  have h4 : Entails.eval a c36 := h 35 (by decide)
  have h5 : Entails.eval a c293 := h 292 (by decide)
  have h6 : Entails.eval a c138 := h 137 (by decide)
  have h7 : Entails.eval a c67 := h 66 (by decide)
  have h8 : Entails.eval a c1 := h 0 (by decide)
  have h9 : Entails.eval a c294 := h 293 (by decide)
  have h10 : Entails.eval a c239 := h 238 (by decide)
  have h11 : Entails.eval a c243 := h 242 (by decide)
  have h12 : Entails.eval a c203 := h 202 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c617 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨17, by decide⟩, false), (⟨49, by decide⟩, false), (⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f617 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c8, some c36, some c602, some c224, some c222, some c85, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨17, by decide⟩, true)), some (DefaultClause.unit (⟨49, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p617 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked617 : lratChecker f617 p617 = .success := by decide +kernel
theorem unsat617 : Unsatisfiable (PosFin 57) f617 := by
  apply lratCheckerSound f617 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p617
  · intro a ha; simp [p617] at ha; subst a; trivial
  · exact checked617
theorem derived617 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c617 := by
  apply localUnsat_implies_entails f617 [c26, c8, c36, c602, c224, c222, c85] c617 unsat617 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c602 := derived602 a h
  have h4 : Entails.eval a c224 := h 223 (by decide)
  have h5 : Entails.eval a c222 := h 221 (by decide)
  have h6 : Entails.eval a c85 := h 84 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c618 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨4, by decide⟩, true), (⟨2, by decide⟩, false), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f618 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c616, some c54, some c19, some c617, some c437, some c242, some c89, some c32, some c224, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨2, by decide⟩, true)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p618 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked618 : lratChecker f618 p618 = .success := by decide +kernel
theorem unsat618 : Unsatisfiable (PosFin 57) f618 := by
  apply lratCheckerSound f618 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p618
  · intro a ha; simp [p618] at ha; subst a; trivial
  · exact checked618
theorem derived618 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c618 := by
  apply localUnsat_implies_entails f618 [c616, c54, c19, c617, c437, c242, c89, c32, c224] c618 unsat618 (by rfl) a
  have h0 : Entails.eval a c616 := derived616 a h
  have h1 : Entails.eval a c54 := h 53 (by decide)
  have h2 : Entails.eval a c19 := h 18 (by decide)
  have h3 : Entails.eval a c617 := derived617 a h
  have h4 : Entails.eval a c437 := derived437 a h
  have h5 : Entails.eval a c242 := h 241 (by decide)
  have h6 : Entails.eval a c89 := h 88 (by decide)
  have h7 : Entails.eval a c32 := h 31 (by decide)
  have h8 : Entails.eval a c224 := h 223 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c619 : DefaultClause 57 := directClause [(⟨4, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f619 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c615, some c547, some c595, some c618, some (DefaultClause.unit (⟨4, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p619 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4]]
theorem checked619 : lratChecker f619 p619 = .success := by decide +kernel
theorem unsat619 : Unsatisfiable (PosFin 57) f619 := by
  apply lratCheckerSound f619 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p619
  · intro a ha; simp [p619] at ha; subst a; trivial
  · exact checked619
theorem derived619 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c619 := by
  apply localUnsat_implies_entails f619 [c615, c547, c595, c618] c619 unsat619 (by rfl) a
  have h0 : Entails.eval a c615 := derived615 a h
  have h1 : Entails.eval a c547 := derived547 a h
  have h2 : Entails.eval a c595 := derived595 a h
  have h3 : Entails.eval a c618 := derived618 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> assumption
def c620 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨33, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f620 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c615, some c19, some c547, some c619, some c98, some c437, some c240, some c242, some c88, some c548, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p620 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
theorem checked620 : lratChecker f620 p620 = .success := by decide +kernel
theorem unsat620 : Unsatisfiable (PosFin 57) f620 := by
  apply lratCheckerSound f620 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p620
  · intro a ha; simp [p620] at ha; subst a; trivial
  · exact checked620
theorem derived620 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c620 := by
  apply localUnsat_implies_entails f620 [c615, c19, c547, c619, c98, c437, c240, c242, c88, c548] c620 unsat620 (by rfl) a
  have h0 : Entails.eval a c615 := derived615 a h
  have h1 : Entails.eval a c19 := h 18 (by decide)
  have h2 : Entails.eval a c547 := derived547 a h
  have h3 : Entails.eval a c619 := derived619 a h
  have h4 : Entails.eval a c98 := h 97 (by decide)
  have h5 : Entails.eval a c437 := derived437 a h
  have h6 : Entails.eval a c240 := h 239 (by decide)
  have h7 : Entails.eval a c242 := h 241 (by decide)
  have h8 : Entails.eval a c88 := h 87 (by decide)
  have h9 : Entails.eval a c548 := derived548 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c621 : DefaultClause 57 := directClause [(⟨33, by decide⟩, true), (⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f621 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c619, some c98, some c615, some c19, some c620, some c36, some c35, some c243, some (DefaultClause.unit (⟨33, by decide⟩, false)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p621 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9]]
theorem checked621 : lratChecker f621 p621 = .success := by decide +kernel
theorem unsat621 : Unsatisfiable (PosFin 57) f621 := by
  apply lratCheckerSound f621 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p621
  · intro a ha; simp [p621] at ha; subst a; trivial
  · exact checked621
theorem derived621 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c621 := by
  apply localUnsat_implies_entails f621 [c547, c619, c98, c615, c19, c620, c36, c35, c243] c621 unsat621 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c619 := derived619 a h
  have h2 : Entails.eval a c98 := h 97 (by decide)
  have h3 : Entails.eval a c615 := derived615 a h
  have h4 : Entails.eval a c19 := h 18 (by decide)
  have h5 : Entails.eval a c620 := derived620 a h
  have h6 : Entails.eval a c36 := h 35 (by decide)
  have h7 : Entails.eval a c35 := h 34 (by decide)
  have h8 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c622 : DefaultClause 57 := directClause [(⟨24, by decide⟩, true), (⟨33, by decide⟩, false), (⟨7, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f622 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c26, some c8, some c36, some c35, some c138, some c243, some c1, some (DefaultClause.unit (⟨24, by decide⟩, false)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p622 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked622 : lratChecker f622 p622 = .success := by decide +kernel
theorem unsat622 : Unsatisfiable (PosFin 57) f622 := by
  apply lratCheckerSound f622 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p622
  · intro a ha; simp [p622] at ha; subst a; trivial
  · exact checked622
theorem derived622 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c622 := by
  apply localUnsat_implies_entails f622 [c26, c8, c36, c35, c138, c243, c1] c622 unsat622 (by rfl) a
  have h0 : Entails.eval a c26 := h 25 (by decide)
  have h1 : Entails.eval a c8 := h 7 (by decide)
  have h2 : Entails.eval a c36 := h 35 (by decide)
  have h3 : Entails.eval a c35 := h 34 (by decide)
  have h4 : Entails.eval a c138 := h 137 (by decide)
  have h5 : Entails.eval a c243 := h 242 (by decide)
  have h6 : Entails.eval a c1 := h 0 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c623 : DefaultClause 57 := directClause [(⟨54, by decide⟩, true), (⟨24, by decide⟩, false), (⟨5, by decide⟩, true), (⟨6, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f623 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c88, some c452, some (DefaultClause.unit (⟨54, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨6, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p623 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2]]
theorem checked623 : lratChecker f623 p623 = .success := by decide +kernel
theorem unsat623 : Unsatisfiable (PosFin 57) f623 := by
  apply lratCheckerSound f623 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p623
  · intro a ha; simp [p623] at ha; subst a; trivial
  · exact checked623
theorem derived623 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c623 := by
  apply localUnsat_implies_entails f623 [c88, c452] c623 unsat623 (by rfl) a
  have h0 : Entails.eval a c88 := h 87 (by decide)
  have h1 : Entails.eval a c452 := derived452 a h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> assumption
def c624 : DefaultClause 57 := directClause [(⟨7, by decide⟩, true), (⟨8, by decide⟩, true), (⟨34, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f624 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c547, some c619, some c97, some c98, some c615, some c621, some c622, some c623, some c549, some c28, some c34, some c33, some c243, some (DefaultClause.unit (⟨7, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false)), some (DefaultClause.unit (⟨34, by decide⟩, false))]
def p624 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]]
theorem checked624 : lratChecker f624 p624 = .success := by decide +kernel
theorem unsat624 : Unsatisfiable (PosFin 57) f624 := by
  apply lratCheckerSound f624 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p624
  · intro a ha; simp [p624] at ha; subst a; trivial
  · exact checked624
theorem derived624 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c624 := by
  apply localUnsat_implies_entails f624 [c547, c619, c97, c98, c615, c621, c622, c623, c549, c28, c34, c33, c243] c624 unsat624 (by rfl) a
  have h0 : Entails.eval a c547 := derived547 a h
  have h1 : Entails.eval a c619 := derived619 a h
  have h2 : Entails.eval a c97 := h 96 (by decide)
  have h3 : Entails.eval a c98 := h 97 (by decide)
  have h4 : Entails.eval a c615 := derived615 a h
  have h5 : Entails.eval a c621 := derived621 a h
  have h6 : Entails.eval a c622 := derived622 a h
  have h7 : Entails.eval a c623 := derived623 a h
  have h8 : Entails.eval a c549 := derived549 a h
  have h9 : Entails.eval a c28 := h 27 (by decide)
  have h10 : Entails.eval a c34 := h 33 (by decide)
  have h11 : Entails.eval a c33 := h 32 (by decide)
  have h12 : Entails.eval a c243 := h 242 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c625 : DefaultClause 57 := directClause [(⟨21, by decide⟩, true), (⟨24, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f625 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c28, some c23, some c5, some c240, some c21, some c3, some c144, some (DefaultClause.unit (⟨21, by decide⟩, false)), some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false))]
def p625 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7]]
theorem checked625 : lratChecker f625 p625 = .success := by decide +kernel
theorem unsat625 : Unsatisfiable (PosFin 57) f625 := by
  apply lratCheckerSound f625 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p625
  · intro a ha; simp [p625] at ha; subst a; trivial
  · exact checked625
theorem derived625 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c625 := by
  apply localUnsat_implies_entails f625 [c28, c23, c5, c240, c21, c3, c144] c625 unsat625 (by rfl) a
  have h0 : Entails.eval a c28 := h 27 (by decide)
  have h1 : Entails.eval a c23 := h 22 (by decide)
  have h2 : Entails.eval a c5 := h 4 (by decide)
  have h3 : Entails.eval a c240 := h 239 (by decide)
  have h4 : Entails.eval a c21 := h 20 (by decide)
  have h5 : Entails.eval a c3 := h 2 (by decide)
  have h6 : Entails.eval a c144 := h 143 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
def c626 : DefaultClause 57 := directClause [(⟨24, by decide⟩, false), (⟨33, by decide⟩, false), (⟨3, by decide⟩, true), (⟨5, by decide⟩, true), (⟨1, by decide⟩, true), (⟨8, by decide⟩, true)] (by decide +kernel) (by decide +kernel)
def f626 : DefaultFormula 57 := DefaultFormula.ofArray #[none, some c625, some c249, some c21, some c3, some c291, some c134, some c61, some c1, some c237, some c225, some c81, some (DefaultClause.unit (⟨24, by decide⟩, true)), some (DefaultClause.unit (⟨33, by decide⟩, true)), some (DefaultClause.unit (⟨3, by decide⟩, false)), some (DefaultClause.unit (⟨5, by decide⟩, false)), some (DefaultClause.unit (⟨1, by decide⟩, false)), some (DefaultClause.unit (⟨8, by decide⟩, false))]
def p626 : List (Action (DefaultClause 57) (PosFin 57)) := [.addEmpty 0 #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]]
theorem checked626 : lratChecker f626 p626 = .success := by decide +kernel
theorem unsat626 : Unsatisfiable (PosFin 57) f626 := by
  apply lratCheckerSound f626 (DefaultFormula.readyForRupAdd_ofArray _) (DefaultFormula.readyForRatAdd_ofArray _) p626
  · intro a ha; simp [p626] at ha; subst a; trivial
  · exact checked626
theorem derived626 (a : PosFin 57 → Bool) (h : InputSat a) : Entails.eval a c626 := by
  apply localUnsat_implies_entails f626 [c625, c249, c21, c3, c291, c134, c61, c1, c237, c225, c81] c626 unsat626 (by rfl) a
  have h0 : Entails.eval a c625 := derived625 a h
  have h1 : Entails.eval a c249 := h 248 (by decide)
  have h2 : Entails.eval a c21 := h 20 (by decide)
  have h3 : Entails.eval a c3 := h 2 (by decide)
  have h4 : Entails.eval a c291 := h 290 (by decide)
  have h5 : Entails.eval a c134 := h 133 (by decide)
  have h6 : Entails.eval a c61 := h 60 (by decide)
  have h7 : Entails.eval a c1 := h 0 (by decide)
  have h8 : Entails.eval a c237 := h 236 (by decide)
  have h9 : Entails.eval a c225 := h 224 (by decide)
  have h10 : Entails.eval a c81 := h 80 (by decide)
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
#print axioms derived626

end CochromaticTwenty.Certificates.B16_0_1
